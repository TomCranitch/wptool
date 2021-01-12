package wptool

object Block {
  def empty: Block = Block("empty", "?", Nil, Nil, false)

  private var currName = 'A'
  def nextName = {
    currName = (currName + 1).toChar
    currName.toString
  }
}

sealed trait Statement extends beaver.Symbol {
  var line: (String, Int) = ("", 0)
  def setLine(block: Block, line: Int) = this.line = (block.label, line)
}

case object Malformed extends Statement {
  def self: Malformed.type = this
}

case class Block(
    label: String,
    name: String,
    statements: List[Statement],
    children: List[Block],
    atomic: Boolean
) extends Statement {
  def this(label: String, statements: Array[Statement]) =
    this(label, Block.nextName, statements.toList, List(), false)
  def this(
      label: String,
      statements: List[Statement],
      children: List[Block],
      atomic: Boolean = false
  ) = this(label, Block.nextName, statements.toList, children, atomic)
  def prepend(statement: Statement) =
    this.copy(statements = statement +: statements)

  override def toString: String =
    name + "(" + label + "): [" + children
      .map(b => b.name)
      .mkString(", ") + "] {\n" + statements.mkString(";\n") + "\n}"
}

case class Assignment(lhs: Id, expression: Expression) extends Statement {
  def this(lhs: String, expression: Expression) =
    this(new Id(lhs, false, false), expression)
  override def toString: String = lhs + " = " + expression
}

case class ArrayAssignment(lhs: IdAccess, expression: Expression)
    extends Statement {
  def this(name: String, index: Expression, expression: Expression) =
    this(new IdAccess(new Id(name, false, false), index), expression)
  override def toString: String =
    lhs.ident + "[" + lhs.index + "]" + " = " + expression
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

case class If(test: Expression, left: Block, right: Option[Block])
    extends Statement {
  def this(test: Expression, left: Block) = this(test, left, None)
  def this(test: Expression, left: Block, right: Block) =
    this(test, left, Some(right))
}

case class Guard(test: Expression) extends Statement {
  override def toString: String = "guard " + test
}

case class While(
    test: Expression,
    invariant: Expression,
    gamma: List[GammaMapping],
    nonblocking: Option[Set[Id]],
    body: Statement
) extends Statement {
  def this(test: Expression, body: Statement) =
    this(test, Const._true, List(), None, body)
  def this(test: Expression, invariant: Expression, body: Statement) =
    this(test, invariant, List(), None, body)
  def this(
      test: Expression,
      invariant: Expression,
      gamma: Array[GammaMapping],
      body: Statement
  ) = this(test, invariant, gamma.toList, None, body)
}

case class DoWhile(
    test: Expression,
    invariant: Expression,
    gamma: List[GammaMapping],
    nonblocking: Option[Set[Id]],
    body: Statement
) extends Statement {
  def this(test: Expression, invariant: Expression, body: Statement) =
    this(test, invariant, List(), None, body)
  def this(
      test: Expression,
      invariant: Expression,
      gamma: Array[GammaMapping],
      body: Statement
  ) = this(test, invariant, gamma.toList, None, body)
}

case class Atomic(statements: List[Statement]) extends Statement {
  def self: Atomic = this

  override def toString: String = "<" + statements.mkString(",") + ">"
}

case class Assume(expression: Expression) extends Statement {
  def self: Assume = this
}

case class Assert(expression: Expression, checkStableR: Boolean = false)
    extends Statement {
  def self: Assert = this
}

case class Havoc() extends Statement {
  def self = this
}
