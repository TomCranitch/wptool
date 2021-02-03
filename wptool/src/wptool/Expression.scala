package wptool

import scala.reflect.runtime.universe.{TypeTag, typeOf}

object Type extends Enumeration {
  type Type = Value
  val TBool, TInt = Value
}

trait Expression extends beaver.Symbol {
  // returns all vars in the expression, does NOT include array indices
  def vars: Set[Var]
  // returns all vars in the expression, does NOT include array indices
  def ids: Set[Id]
  def subst(su: Subst): Expression
  def arrays: Set[VarAccess]

  def expType: Type.Type
}

case class Lit(arg: Int) extends Expression {
  override def toString: String = arg.toString
  override def vars = Set()
  override def ids = Set()
  override def arrays = Set()
  override def subst(su: Subst): Lit = this
  override def expType = Type.TInt
}

trait Identifier extends Expression {
  def toPrime: Identifier
  def toGamma: Identifier
  def toVar(state: State): Variable
  def getBase: Identifier
}

trait Variable extends Expression {
  def toPrime(state: State): Variable
  def toGamma(state: State): Variable
  def toNought: Variable
  def ident: Id
  def getBase: Variable
  def resetIndex: Variable
}

// id parsed from input - need to convert to Var before use in predicates etc.
case class Id(name: String, override val expType: Type.Type, prime: Boolean, gamma: Boolean, nought: Boolean) extends Identifier {
  /* override def toString: String =
    (if (gamma) "Gamma_" else "") + name + (if (prime) "'" else "") + (if (nought) "⁰" else "") */
  override def vars = throw new Error("Tried to get var from id")
  override def ids = Set(this)
  override def arrays = Set()
  override def subst(su: Subst) = throw new Error(s"tried to subst id $this")
  def toVar(state: State) = Var(this, getIndex(state))
  def toPrime = this.copy(prime = true)
  // TODO change type
  def toGamma = Id(name, Type.TBool, prime, true, nought)

  def getIndex(state: State) = {
    // println(state.indicies.map { case (k, v) => (k, k == this.copy(gamma = false, expType = Type.TInt)) })
    // println(this.copy(gamma = false, expType = Type.TInt))
    if (!gamma) state.indicies.getOrElse(this, throw new Error(s"Index not found for var $this with type $expType"))
    // TODO change Type.TInt
    else
      state.indicies.getOrElse(
        this.copy(gamma = false, expType = Type.TInt),
        throw new Error(s"Index not found for gamma var $this with type $expType")
      )
  }

  // TODO use actual type
  override def getBase = Id(name, Type.TInt, false, false, false)
}

object Id {
  // TODO change to bool
  val tmpId = Id("tmp", Type.TInt, false, false, false)
  val indexId = Id("_i", Type.TInt, false, false, false)
}

case class Var(ident: Id, index: Int, tmp: Boolean = false) extends Variable {
  override def toString: String =
    (if (tmp) "tmp_" else "") + ident.toString __ index
  override def vars = Set(this)
  override def ids = Set(this.ident)
  override def arrays = Set()
  override def subst(su: Subst) = su.get(this) match {
    case Some(Left(e: Expression)) => e
    case Some(Right(_)) =>
      throw new Error(s"Tried to subst var $this with index")
    case None => this
  }
  def toPrime(state: State) =
    this.copy(ident = ident.toPrime).updateIndex(state)
  def toGamma(state: State) = this.copy(ident = ident.toGamma)
  def toNought = this.copy(ident = ident.copy(nought = true))

  override def expType = ident.expType

  private def updateIndex(state: State) =
    this.copy(index = this.ident.getIndex(state))

  override def getBase = this.copy(ident = ident.getBase)
  override def resetIndex = this.copy(index = 0)
}

case class IdAccess(ident: Id, index: Expression) extends Expression with Identifier {
  def this(name: String, index: Expression) = this(Id(name, Type.TInt, false, false, false), index)
  def this(name: String, prime: Boolean, gamma: Boolean, index: Expression) = this(Id(name, Type.TInt, prime, gamma, false), index)
  def vars = index.vars
  def ids = index.ids
  def arrays = throw new Error("tried to get array from IdAccess")
  def subst(su: Subst) = throw new Error("tried to subst var id")
  override def toString = ident + "[" + index + "]"
  def toGamma = this.copy(ident = ident.toGamma)
  def toPrime = this.copy(ident = ident.toPrime)
  override def expType = ident.expType

  def toVar(state: State) = VarAccess(ident.toVar(state), index)
  def getBase = this.copy(ident = ident.getBase)
}

// array access with Var for use in logical predicates
case class VarAccess(name: Var, index: Expression) extends Variable {
  def vars = index.vars
  def ids = index.ids
  def arrays = Set(this)

  def subst(su: Subst) = {
    val updatedArr = this.copy(index = index.subst(su))
    su.get(name) match {
      case Some(Right((i: Expression, e: Expression))) =>
        VarStore(updatedArr, i, e)
      case Some(Left(v: Var)) => updatedArr.copy(name = v) // to handle priming
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
  override def expType = ident.expType
  override def getBase = this.copy(name = name.getBase)
  override def resetIndex = this.copy(name = name.resetIndex)
}

case class VarStore(array: Expression, index: Expression, exp: Expression) extends Expression {
  def vars = array.vars ++ index.vars ++ exp.vars
  def ids = array.ids ++ index.ids ++ exp.ids
  def arrays = array.arrays ++ index.arrays ++ exp.arrays
  def subst(su: Subst) = VarStore(array.subst(su), index.subst(su), exp.subst(su))
  override def expType = array.expType
}

/*
case class ArrayConstDefault(name: Var, const: Expression) extends Expression {
  def vars = const.vars
  def ids = const.ids ++ name.ids
  def arrays = const.arrays ++ name.arrays
  def subst(su: Subst) = ArrayConstDefault(name, const.subst(su))
  override def expType = name.expType
}
 */

case class PreOp(op: String, override val expType: Type.Type, argType: Type.Type, arg: Expression) extends Expression {
  override def toString: String = "(" + op + " " + arg + ")"
  override def vars = arg.vars
  override def ids = arg.ids
  def arrays = arg.arrays
  def subst(su: Subst) = this.copy(arg = arg.subst(su))
}

case class PostOp(op: String, override val expType: Type.Type, argType: Type.Type, arg: Expression) extends Expression {
  override def toString: String = "(" + arg + " " + op + ")"
  override def vars = arg.vars
  override def ids = arg.ids
  def arrays = arg.arrays
  def subst(su: Subst) = this.copy(arg = arg.subst(su))
}

case class BinOp(op: String, override val expType: Type.Type, argType: Type.Type, arg1: Expression, arg2: Expression) extends Expression {
  // override def toString: String = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def vars = arg1.vars ++ arg2.vars
  override def ids = arg1.ids ++ arg2.ids
  def arrays = arg1.arrays ++ arg2.arrays
  def subst(su: Subst) = this.copy(arg1 = arg1.subst(su), arg2 = arg2.subst(su))
}

object BinOp {
  def pred(op: String, arg1: Expression, arg2: Expression) = BinOp(op, Type.TBool, Type.TBool, arg1, arg2)
}

object Const {
  object _true extends Const("True")
  object _false extends Const("False")
}

case class Const(name: String) extends Expression {
  override def toString: String = name.toString
  override def vars = Set()
  override def ids = Set()
  override def arrays = Set()
  override def subst(su: Subst): Const = this
  override def expType = Type.TBool
}

// TODO change to bool expression
case class CompareAndSwap(x: Id, e1: Expression, e2: Expression) extends Expression {
  def this(x: String, e1: Expression, e2: Expression) = this(new Id(x, Type.TInt, false, false, false), e1, e2)
  override def toString: String = "CAS(" + x + ", " + e1 + ", " + e2 + ")"
  override def vars = e1.vars ++ e2.vars
  override def ids = e1.ids ++ e2.ids
  def arrays = e1.arrays ++ e2.arrays
  override def subst(su: Subst) = this
  override def expType = Type.TInt // TODO
}

case class ForAll(bound: Set[_ <: Expression], body: Expression) extends Expression {
  def this(bound: Array[Expression], body: Expression) = this(bound.toSet, body)
  override def ids = body.ids -- (bound.map(id => id.ids).flatten)
  override def vars = body.vars -- (bound.map(v => v.vars).flatten)
  def arrays = body.arrays -- bound.map(a => a.arrays).flatten
  override def subst(su: Subst) = ForAll(bound, body.subst(su))
  override def toString = s"∀ ${bound.mkString(", ")} : $body"
  override def expType = Type.TBool
}
