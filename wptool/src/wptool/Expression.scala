package wptool

import scala.util.Try

trait Expression extends beaver.Symbol {

  def vars: Set[Var] // returns all vars in the expression, does NOT include array indices
  def ids: Set[Id] // returns all vars in the expression, does NOT include array indices
  def subst(su: Subst): Expression
  def subst(su: Subst, num: Int): Expression

}

trait BoolExpression extends Expression {
  def subst(su: Subst): BoolExpression
  def subst(su: Subst, num: Int): BoolExpression
}

case class Lit(arg: Int) extends Expression {
  override def toString: String = arg.toString
  override def vars: Set[Var] = Set()
  override def ids: Set[Id] = Set()
  override def subst(su: Subst): Lit = this
  override def subst(su: Subst, num: Int): Lit = this.subst(su)
}

trait Identifier {}

// id parsed from input - need to convert to Var before use in predicates etc.
case class Id (name: String, prime: Boolean, gamma: Boolean) extends Expression with Identifier {
  override def toString: String = (if (gamma) "Gamma_" else "") + name + (if (prime) "'" else "")
  override def vars: Set[Var] = throw new Error("Tried to get var from id")
  override def ids: Set[Id] = Set(this)
  override def subst(su: Subst): Expression = throw new Error("tried to subst id") // su.getOrElse(this, this)
  override def subst(su: Subst, num: Int): Expression = this.subst(su)
  def toVar (state: State) = {
    if (!gamma) Var(this, state.indicies.getOrElse(this, -1))
    else Var(this, state.indicies.getOrElse(this.copy(gamma = false), -1))
  }
  def toPrime = this.copy(prime = true)
  def toGamma = this.copy(gamma = true)
}

case class Var (ident: Id, index: Int) extends Expression {
  override def toString: String = ident.toString __ index
  override def vars: Set[Var] = Set(this)
  override def ids: Set[Id] = Set(this.ident)
  override def subst(su: Subst): Expression = su.getOrElse(this, this)
  override def subst(su: Subst, num: Int): Expression = this.subst(su)
  def toPrime = this.copy(ident = ident.toPrime)
  def toGamma = this.copy(ident = ident.toGamma)
}

// object CFence extends Id("cfence", false)


// switching logical variable for CNF format
case class Switch(index: Int) extends BoolExpression {
  override def vars: Set[Var] = Set()
  override def ids: Set[Id] = Set()
  def subst(su: Subst): BoolExpression = this
  def subst(su: Subst, num: Int): BoolExpression = this
}

object Switch {
  var index = 1
  def fresh: Switch = {
    index += 1
    Switch(index)
  }
}

case class MultiSwitch(index: Int) extends Expression {
  override def vars: Set[Var] = Set()
  override def ids: Set[Id] = Set()
  def subst(su: Subst): Expression = this
  def subst(su: Subst, num: Int): Expression = this
}

object MultiSwitch {
  var index = 0
  def fresh: MultiSwitch = {
    index += 1
    MultiSwitch(index)
  }
}

/*
case class not(arg: BoolExpression) extends BoolExpression {
  override def toString = "(! " + arg + ")"
  override def variables: Set[Var] = arg.variables
  def subst(su: Subst) = not(arg.subst(su))
  def subst(su: Subst, num: Int) =  not(arg.subst(su, num))
  override def arrays = arg.arrays
}

case class and(arg1: BoolExpression, arg2: BoolExpression) extends BoolExpression {
  override def toString = "(" + arg1 + " && " + arg2 + ")"
  override def variables: Set[Var] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = and(arg1.subst(su), arg2.subst(su))
  def subst(su: Subst, num: Int) = and(arg1.subst(su, num), arg2.subst(su, num))
  override def arrays = arg1.arrays ++ arg2.arrays
}

case class or(arg1: BoolExpression, arg2: BoolExpression) extends BoolExpression {
  override def toString = "(" + arg1 + " && " + arg2 + ")"
  override def variables: Set[Var] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = or(arg1.subst(su), arg2.subst(su))
  def subst(su: Subst, num: Int) = or(arg1.subst(su, num), arg2.subst(su, num))
  override def arrays = arg1.arrays ++ arg2.arrays
}

case class eq(arg1: Expression, arg2: Expression) extends BoolExpression {
  override def toString = "(" + arg1 + " && " + arg2 + ")"
  override def variables: Set[Var] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = eq(arg1.subst(su), arg2.subst(su))
  def subst(su: Subst, num: Int) = eq(arg1.subst(su, num), arg2.subst(su, num))
  override def arrays = arg1.arrays ++ arg2.arrays
}
 */

case class PreOp(op: String, arg: Expression) extends Expression {
  override def toString: String = "(" + op + " " + arg + ")"
  override def vars: Set[Var] = arg.vars
  override def ids: Set[Id] = arg.ids
  def subst(su: Subst): Expression =  PreOp(op, arg.subst(su))
  def subst(su: Subst, num: Int): Expression =  PreOp(op, arg.subst(su, num))
}

case class PostOp(op: String, arg: Expression) extends Expression {
  override def toString: String = "(" + arg + " " + op + ")"
  override def vars: Set[Var] = arg.vars
  override def ids: Set[Id] = arg.ids
  def subst(su: Subst): Expression = PostOp(op, arg.subst(su))
  def subst(su: Subst, num: Int): Expression =  PostOp(op, arg.subst(su, num))
}

case class BinOp(op: String, arg1: Expression, arg2: Expression) extends Expression {
  override def toString: String = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def vars: Set[Var] = arg1.vars ++ arg2.vars
  override def ids: Set[Id] = arg1.ids ++ arg2.ids
  def subst(su: Subst): Expression = BinOp(op, arg1.subst(su), arg2.subst(su))
  def subst(su: Subst, num: Int): Expression = BinOp(op, arg1.subst(su, num), arg2.subst(su, num))
}

case class Question(test: Expression, left: Expression, right: Expression) extends Expression {
  override def toString: String = "(" + test + " ? " + left + " : " + right + ")"
  override def vars: Set[Var] = test.vars ++ left.vars ++ right.vars
  override def ids: Set[Id] = test.ids ++ left.ids ++ right.ids
  def subst(su: Subst): Expression = Question(test.subst(su), left.subst(su), right.subst(su))
  def subst(su: Subst, num: Int): Expression = Question(test.subst(su, num), left.subst(su, num), right.subst(su, num))
}

/*
case class ForAll(bound: Set[_ <: Expression], body: Expression) extends BoolExpression {
  override def vars: Set[Var] = body.vars -- (bound collect {case x: Id => x})
  def subst(su: Subst): BoolExpression = ForAll(bound, body.subst(su))
  def subst(su: Subst, num: Int): BoolExpression = ForAll(bound, body.subst(su, num))
}

case class Exists(bound: Set[_ <: Expression], body: Expression) extends BoolExpression {
  override def vars: Set[Var] = body.vars -- (bound collect {case x: Id => x})
  def subst(su: Subst): BoolExpression = Exists(bound, body.subst(su))
  def subst(su: Subst, num: Int): BoolExpression = Exists(bound, body.subst(su, num))
}
*/

object Const {
  object _true extends Const("True")
  object _false extends Const("False")
}

case class Const(name: String) extends Expression {
  override def toString: String = name.toString
  override def vars: Set[Var] = Set()
  override def ids: Set[Id] = Set()
  override def subst(su: Subst): Const = this
  override def subst(su: Subst, num: Int): Const = this
}

/*
case class Gamma (vars: Set[Var]) extends Expression {
  def this(id: Id) = this(Set(id))
  def eval (state: State): Security = Try(vars.map(ident => state.Gamma.getOrElse(ident.copy(index = 0), Low)).max).getOrElse(Low)
  override def subst(su: Subst): Gamma = this
  override def subst(su: Subst, num: Int): Gamma = this
  override def variables: Set[Var] = Set()
}
 */

/*
case class CompareAndSwap(x: Id, e1: Expression, e2: Expression) extends Expression {
  def this(x: String, e1: Expression, e2: Expression) = this(new Id(x), e1, e2)
  override def toString: String = "CAS(" + x + ", " + e1 + ", " + e2 + ")"
  override def vars: Set[Var] = Set()
  override def subst(su: Subst): Expression = this
  override def subst(su: Subst, num: Int): Expression = this
}
*/
