package wptool

import scala.reflect.runtime.universe.{TypeTag, typeOf}

trait Type
trait TBool extends Type
trait TInt extends Type

trait Expression[+T <: Type] extends beaver.Symbol {
  // returns all vars in the expression, does NOT include array indices
  def vars: Set[Var[Type]]
  // returns all vars in the expression, does NOT include array indices
  def ids: Set[Id[Type]]
  def subst(su: Subst): Expression[T]
  def arrays: Set[VarAccess[Type]]
}

case class Lit(arg: Int) extends Expression[TInt] {
  override def toString: String = arg.toString
  override def vars = Set()
  override def ids = Set()
  override def arrays = Set()
  override def subst(su: Subst): Lit = this
}

trait Identifier[+T <: Type] extends Expression[T] {
  def toPrime: Identifier[T]
  def toGamma: Identifier[TBool]
  def toVar(state: State): Variable[T]
}

trait Variable[+T <: Type] extends Expression[T] {
  def toPrime(state: State): Variable[T]
  def toGamma(state: State): Variable[TBool]
  def toNought: Variable[T]
  def ident: Id[T]
}

// id parsed from input - need to convert to Var before use in predicates etc.
case class Id[+T <: Type](name: String, prime: Boolean, gamma: Boolean, nought: Boolean) extends Expression[T] with Identifier[T] {
  override def toString: String =
    (if (gamma) "Gamma_" else "") + name + (if (prime) "'" else "") + (if (nought) "⁰" else "")
  override def vars = throw new Error("Tried to get var from id")
  override def ids = Set(this)
  override def arrays = Set()
  override def subst(su: Subst) = throw new Error(s"tried to subst id $this")
  def toVar(state: State) = Var(this, getIndex(state))
  def toPrime = this.copy(prime = true)
  // TODO change type
  def toGamma = Id[TBool](name, prime, true, nought)

  def getIndex(state: State) = {
    if (!gamma) state.indicies.getOrElse(this, -1)
    else state.indicies.getOrElse(this.copy(gamma = false), -1)
  }
}

object Id {
  val tmpId = Id[TBool]("tmp", false, false, false)
  val indexId = Id[TInt]("_i", false, false, false)
}

case class Var[+T <: Type](ident: Id[T], index: Int, tmp: Boolean = false) extends Expression[T] with Variable[T] {
  override def toString: String =
    (if (tmp) "tmp_" else "") + ident.toString __ index
  override def vars = Set(this)
  override def ids = Set(this.ident)
  override def arrays = Set()
  override def subst(su: Subst) = su.get(this) match {
    case Some(Left(e: Expression[T])) => e
    case Some(Right(_)) =>
      throw new Error(s"Tried to subst var $this with index")
    case None => this
  }
  def toPrime(state: State) =
    this.copy(ident = ident.toPrime).updateIndex(state)
  def toGamma(state: State) = this.copy(ident = ident.toGamma)
  def toNought = this.copy(ident = ident.copy(nought = true))

  private def updateIndex(state: State) =
    this.copy(index = this.ident.getIndex(state))
}

case class IdAccess[+T <: Type](ident: Id[T], index: Expression[TInt]) extends Expression[T] with Identifier[T] {
  def this(name: String, index: Expression[TInt]) = this(Id[T](name, false, false, false), index)
  def this(name: String, prime: Boolean, gamma: Boolean, index: Expression[TInt]) = this(Id[T](name, prime, gamma, false), index)
  def vars = index.vars
  def ids = index.ids
  def arrays = throw new Error("tried to get array from IdAccess")
  def subst(su: Subst) = throw new Error("tried to subst var id")
  override def toString = ident + "[" + index + "]"
  def toGamma = this.copy(ident = ident.toGamma)
  def toPrime = this.copy(ident = ident.toPrime)

  // TODO index to var
  def toVar(state: State) = VarAccess(ident.toVar(state), index)
}

// array access with Var for use in logical predicates
case class VarAccess[+T <: Type](name: Var[T], index: Expression[TInt]) extends Expression[T] with Variable[T] {
  def vars = index.vars
  def ids = index.ids
  def arrays = Set(this)

  def subst(su: Subst) = {
    val updatedArr = this.copy(index = index.subst(su))
    su.get(name) match {
      case Some(Right((i: Expression[TInt], e: Expression[T]))) =>
        VarStore(updatedArr, i, e)
      case Some(Left(v: Var[T])) => updatedArr.copy(name = v) // to handle priming
      case Some(Left(_)) =>
        throw new Error("Tried to subst varaccess without index")
      case None => updatedArr
    }
  }

  override def toString = name + "[" + index + "]"
  def toGamma(state: State) = this.copy(name = name.toGamma(state))
  def toPrime(state: State) = this.copy(name = name.toPrime(state))
  def toNought = this.copy(name = name.toNought)
  def ident = name.ident
}

case class VarStore[T <: Type](array: Expression[T], index: Expression[TInt], exp: Expression[T]) extends Expression[T] {
  def vars = array.vars ++ index.vars ++ exp.vars
  def ids = array.ids ++ index.ids ++ exp.ids
  def arrays = array.arrays ++ index.arrays ++ exp.arrays
  def subst(su: Subst) = VarStore(array.subst(su), index.subst(su), exp.subst(su))
}

case class ArrayConstDefault[T <: Type](name: Var[T], const: Expression[T]) extends Expression[T] {
  def vars = const.vars
  def ids = const.ids ++ name.ids
  def arrays = const.arrays ++ name.arrays
  def subst(su: Subst) = ArrayConstDefault(name, const.subst(su))
}

case class PreOp[Arg <: Type, Ret <: Type](op: String, arg: Expression[Arg]) extends Expression[Ret] {
  override def toString: String = "(" + op + " " + arg + ")"
  override def vars = arg.vars
  override def ids = arg.ids
  def arrays = arg.arrays
  def subst(su: Subst) = PreOp(op, arg.subst(su))
}

case class PostOp[Arg <: Type, Ret <: Type](op: String, arg: Expression[Arg]) extends Expression[Ret] {
  override def toString: String = "(" + arg + " " + op + ")"
  override def vars = arg.vars
  override def ids = arg.ids
  def arrays = arg.arrays
  def subst(su: Subst) = PostOp(op, arg.subst(su))
}

case class BinOp[Arg <: Type, Ret <: Type](op: String, arg1: Expression[Arg], arg2: Expression[Arg]) extends Expression[Ret] {
  override def toString: String = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def vars = arg1.vars ++ arg2.vars
  override def ids = arg1.ids ++ arg2.ids
  def arrays = arg1.arrays ++ arg2.arrays
  def subst(su: Subst) = BinOp(op, arg1.subst(su), arg2.subst(su))
}

object Const {
  object _true extends Const("True")
  object _false extends Const("False")
}

case class Const(name: String) extends Expression[TBool] {
  override def toString: String = name.toString
  override def vars = Set()
  override def ids = Set()
  override def arrays = Set()
  override def subst(su: Subst): Const = this
}

// TODO change to bool expression
case class CompareAndSwap(x: Id[TInt], e1: Expression[TInt], e2: Expression[TInt]) extends Expression[TBool] {
  def this(x: String, e1: Expression[TInt], e2: Expression[TInt]) =
    this(new Id(x, false, false, false), e1, e2)
  override def toString: String = "CAS(" + x + ", " + e1 + ", " + e2 + ")"
  override def vars = e1.vars ++ e2.vars
  override def ids = e1.ids ++ e2.ids
  def arrays = e1.arrays ++ e2.arrays
  override def subst(su: Subst) = this
}

case class ForAll(bound: Set[_ <: Expression[TBool]], body: Expression[TBool]) extends Expression[TBool] {
  def this(bound: Array[Expression[TBool]], body: Expression[TBool]) = this(bound.toSet, body)
  override def ids = body.ids -- (bound.map(id => id.ids).flatten)
  override def vars = body.vars -- (bound.map(v => v.vars).flatten)
  def arrays = body.arrays -- bound.map(a => a.arrays).flatten
  override def subst(su: Subst) = ForAll(bound, body.subst(su))
  override def toString = s"∀ ${bound.mkString(", ")} : $body"
}
