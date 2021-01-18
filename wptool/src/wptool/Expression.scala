package wptool

import scala.util.Try

trait Expression extends beaver.Symbol {
  def vars: Set[
    Var
  ] // returns all vars in the expression, does NOT include array indices
  def ids: Set[
    Id
  ] // returns all vars in the expression, does NOT include array indices
  def subst(su: Subst): Expression

  def arrays: Set[VarAccess]
}

trait BoolExpression extends Expression {
  def subst(su: Subst): BoolExpression
}

case class Lit(arg: Int) extends Expression {
  override def toString: String = arg.toString
  override def vars: Set[Var] = Set()
  override def ids: Set[Id] = Set()
  override def arrays: Set[VarAccess] = Set()
  override def subst(su: Subst): Lit = this
}

trait Identifier extends Expression {
  def toPrime: Identifier
  def toGamma: Identifier
  def toVar(state: State): Variable
}
trait Variable extends Expression {
  def toPrime(state: State): Variable
  def toGamma(state: State): Variable
  def toNought: Variable
  def ident: Id
}

// id parsed from input - need to convert to Var before use in predicates etc.
case class Id(name: String, prime: Boolean, gamma: Boolean, nought: Boolean) extends Expression with Identifier {
  override def toString: String =
    (if (gamma) "Gamma_" else "") + name + (if (prime) "'" else "") + (if (nought) "⁰" else "")
  override def vars: Set[Var] = throw new Error("Tried to get var from id")
  override def ids: Set[Id] = Set(this)
  override def arrays: Set[VarAccess] = Set()
  override def subst(su: Subst): Expression =
    throw new Error(s"tried to subst id $this")
  def toVar(state: State) = Var(this, getIndex(state))
  def toPrime = this.copy(prime = true)
  def toGamma = this.copy(gamma = true)

  def getIndex(state: State) = {
    if (!gamma) state.indicies.getOrElse(this, -1)
    else state.indicies.getOrElse(this.copy(gamma = false), -1)
  }
}

object Id {
  val tmpId = Id("tmp", false, false, false)
  val indexId = Id("_i", false, false, false)
}

case class Var(ident: Id, index: Int, tmp: Boolean = false) extends Expression with Variable {
  override def toString: String =
    (if (tmp) "tmp_" else "") + ident.toString __ index
  override def vars: Set[Var] = Set(this)
  override def ids: Set[Id] = Set(this.ident)
  override def arrays: Set[VarAccess] = Set()
  override def subst(su: Subst): Expression = su.get(this) match {
    case Some(Left(e)) => e
    case Some(Right(_)) =>
      throw new Error(s"Tried to subst var $this with index")
    case None => this
  }
  def toPrime(state: State) =
    this.copy(ident = ident.toPrime).updateIndex(state)
  def toGamma(state: State) =
    this.copy(ident = ident.toGamma).updateIndex(state)
  def toNought = this.copy(ident = ident.copy(nought = true))

  private def updateIndex(state: State) =
    this.copy(index = this.ident.getIndex(state))
}

case class IdAccess(ident: Id, index: Expression) extends Expression with Identifier {
  def this(name: String, index: Expression) =
    this(Id(name, false, false, false), index)
  def this(name: String, prime: Boolean, gamma: Boolean, index: Expression) =
    this(Id(name, prime, gamma, false), index)
  // TODO is this enough??? i feel like it should return the access
  def vars: Set[Var] = index.vars
  def ids: Set[Id] = index.ids
  def arrays = throw new Error("tried to get array from IdAccess")
  def subst(su: Subst): Expression = throw new Error("tried to subst var id")
  override def toString = ident + "[" + index + "]"
  def toGamma = this.copy(ident = ident.toGamma)
  def toPrime = this.copy(ident = ident.toPrime)

  // TODO index to var
  def toVar(state: State) = VarAccess(ident.toVar(state), index)
}

// array access with Var for use in logical predicates
case class VarAccess(name: Var, index: Expression) extends Expression with Variable {
  def vars: Set[Var] = index.vars
  def ids: Set[Id] = index.ids
  def arrays: Set[VarAccess] = Set(this)
  def subst(su: Subst) = {
    val updatedArr = this.copy(index = index.subst(su))
    su.get(name) match {
      case Some(Right((e, i))) =>
        VarStore(updatedArr, e, i, name.ident.name, name.ident.gamma)
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
}

case class VarStore(
    array: Expression,
    index: Expression,
    exp: Expression,
    name: String,
    isBool: Boolean = false
) extends Expression {
  def vars: Set[Var] = array.vars ++ index.vars ++ exp.vars
  def ids: Set[Id] = array.ids ++ index.ids ++ exp.ids
  def arrays: Set[VarAccess] = array.arrays ++ index.arrays ++ exp.arrays
  // TODO
  // TODO maybe make it Map(Var -> (index, exp))
  def subst(su: Subst) =
    VarStore(array.subst(su), index.subst(su), exp.subst(su), name, isBool)
}

case class ArrayConstDefault(name: Var, const: Expression) extends Expression {
  def vars = const.vars
  def ids = const.ids ++ name.ids
  def arrays: Set[VarAccess] = const.arrays ++ name.arrays
  def subst(su: Subst) = ArrayConstDefault(name, const.subst(su))
}

case class PreOp(op: String, arg: Expression) extends Expression {
  override def toString: String = "(" + op + " " + arg + ")"
  override def vars: Set[Var] = arg.vars
  override def ids: Set[Id] = arg.ids
  def arrays: Set[VarAccess] = arg.arrays
  def subst(su: Subst): Expression = PreOp(op, arg.subst(su))
}

case class PostOp(op: String, arg: Expression) extends Expression {
  override def toString: String = "(" + arg + " " + op + ")"
  override def vars: Set[Var] = arg.vars
  override def ids: Set[Id] = arg.ids
  def arrays: Set[VarAccess] = arg.arrays
  def subst(su: Subst): Expression = PostOp(op, arg.subst(su))
}

case class BinOp(op: String, arg1: Expression, arg2: Expression) extends Expression {
  override def toString: String = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def vars: Set[Var] = arg1.vars ++ arg2.vars
  override def ids: Set[Id] = arg1.ids ++ arg2.ids
  def arrays: Set[VarAccess] = arg1.arrays ++ arg2.arrays
  def subst(su: Subst): Expression = BinOp(op, arg1.subst(su), arg2.subst(su))
}

case class Question(test: Expression, left: Expression, right: Expression) extends Expression {
  override def toString: String =
    "(" + test + " ? " + left + " : " + right + ")"
  override def vars: Set[Var] = test.vars ++ left.vars ++ right.vars
  override def ids: Set[Id] = test.ids ++ left.ids ++ right.ids
  def arrays: Set[VarAccess] = test.arrays ++ left.arrays ++ right.arrays
  def subst(su: Subst): Expression =
    Question(test.subst(su), left.subst(su), right.subst(su))
}

object Const {
  object _true extends Const("True")
  object _false extends Const("False")
}

case class Const(name: String) extends Expression {
  override def toString: String = name.toString
  override def vars: Set[Var] = Set()
  override def ids: Set[Id] = Set()
  override def arrays: Set[VarAccess] = Set()
  override def subst(su: Subst): Const = this
}

case class CompareAndSwap(x: Id, e1: Expression, e2: Expression) extends Expression {
  def this(x: String, e1: Expression, e2: Expression) =
    this(new Id(x, false, false, false), e1, e2)
  override def toString: String = "CAS(" + x + ", " + e1 + ", " + e2 + ")"
  override def vars: Set[Var] = e1.vars ++ e2.vars
  override def ids: Set[Id] = e1.ids ++ e2.ids
  def arrays: Set[VarAccess] = e1.arrays ++ e2.arrays
  override def subst(su: Subst): Expression = this
}

case class ForAll(bound: Set[_ <: Expression], body: Expression) extends BoolExpression {
  def this(bound: Array[Expression], body: Expression) = this(bound.toSet, body)
  override def ids = body.ids -- (bound.map(id => id.ids).flatten)
  override def vars = body.vars -- (bound.map(v => v.vars).flatten)
  def arrays: Set[VarAccess] = body.arrays -- bound.map(a => a.arrays).flatten
  override def subst(su: Subst) = ForAll(bound, body.subst(su))
  override def toString = s"∀ ${bound.mkString(", ")} : $body"
}
