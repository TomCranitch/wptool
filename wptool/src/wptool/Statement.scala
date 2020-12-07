package wptool

object Block {
  def empty: Block = Block("empty", "?", Nil, Nil)

  private var currName = 'A'
  def nextName = {
    currName = (currName + 1).toChar
    currName.toString
  }
}

sealed trait Statement extends beaver.Symbol {
  def line: Int = beaver.Symbol.getLine(this.getStart)
}

case object Malformed extends Statement {
  def self: Malformed.type = this
}

case class Block(label: String, name: String, statements: List[Statement], children: List[Block]) extends Statement {
  def this(label: String, statements: Array[Statement]) = this(label, Block.nextName, statements.toList, List())
  def this(label: String, statements: List[Statement], children: List[Block]) = this(label, Block.nextName, statements.toList, children)
  def prepend(statement: Statement) = this.copy(statements = statement +: statements)

  override def toString: String = name + "(" + label + "): [" + children.map(b => b.name).mkString(", ") + "] {\n" + statements.mkString(";\n") + "\n}"
}

case class Assignment(lhs: Id, expression: Expression) extends Statement {
  def this(lhs: String, expression: Expression) = this(new Id(lhs, false, false), expression)
  override def toString: String = lhs + " = " + expression
}

case class ArrayAssignment(name: Id, index: Expression, expression: Expression) extends Statement {
  def this(name: String, index: Expression, expression: Expression) = this(new Id(name, false, false), index, expression)
  override def toString: String = name + "[" + index + "]" + " = " + expression
}

/*
case object Break extends Statement {
  def self = this
}

case object Continue extends Statement {
  def self = this
}

case class Return(expression: Option[Expression]) extends Statement {
  def this(expression: Expression) = this(Some(expression))
}

object Return extends (Option[Expression] => Return) {
  val none = Return(None)
}
 */

case object Fence extends Statement {
  def self: Fence.type = this
}

case object ControlFence extends Statement {
  def self: ControlFence.type = this
}

case class If(test: Expression, left: Block, right: Option[Block]) extends Statement {
  def this(test: Expression, left: Block) = this(test, left, None)
  def this(test: Expression, left: Block, right: Block) = this(test, left, Some(right))
}

case class Guard(test: Expression) extends Statement {
  override def toString: String = "guard " + test
}


case class While(test: Expression, invariant: Expression, gamma: List[GammaMapping], nonblocking: Option[Set[Id]], body: Statement) extends Statement {
  def this(test: Expression, body: Statement) = this(test, Const._true, List(), None, body)
  def this(test: Expression, invariant: Expression, body: Statement) = this(test, invariant, List(), None, body)
  def this(test: Expression, invariant: Expression, gamma: Array[GammaMapping], body: Statement) = this(test, invariant, gamma.toList, None, body)
  def this(test: Expression, invariant: Expression, gamma: Array[GammaMapping], nonblocking: Array[Id], body: Statement) = this(test, invariant, gamma.toList, Some(nonblocking.toSet), body)
}

case class DoWhile(test: Expression, invariant: Expression, gamma: List[GammaMapping], nonblocking: Option[Set[Id]], body: Statement) extends Statement {
  def this(test: Expression, invariant: Expression, gamma: Array[GammaMapping], body: Statement) = this(test, invariant, gamma.toList, None, body)
  def this(test: Expression, invariant: Expression, gamma: Array[GammaMapping], nonblocking: Array[Id], body: Statement) = this(test, invariant, gamma.toList, Some(nonblocking.toSet), body)
}

case class Atomic(statements: List[Statement]) extends Statement {
  def self: Atomic = this

  override def toString: String = "<" + statements.mkString(",") + ">"
}

case class Assume (expression: Expression) extends Statement {
  def self: Assume = this
}

case class Assert (expression: Expression, checkStableR: Boolean = false) extends Statement {
  def self: Assert = this
}

case class Havoc () extends Statement {
  def self = this
}
