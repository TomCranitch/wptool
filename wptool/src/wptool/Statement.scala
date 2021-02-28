package wptool

abstract class Stmt(line: (String, Int)) extends beaver.Symbol {
  def incLine: Stmt
  def setLine(line: (String, Int)): Stmt
  def getLine = line

  def blockName: String = line._1
  def toStringWLine = s"$line ${this.toString}"
}

case object Malformed extends Stmt(("", -1)) {
  def self: Malformed.type = this

  def incLine = this
  def setLine(line: (String, Int)) = this
}

case object EmptyStmt extends Stmt(("", -1)) {
  def self: EmptyStmt.type = this

  def incLine = this
  def setLine(line: (String, Int)) = this
}

case class Block(
    label: String,
    name: String,
    statements: List[Stmt],
    children: List[Block],
    atomic: Boolean
) extends beaver.Symbol {
  // Don't need to process array as this is for unprocessed blocks
  def this(label: String, statements: Array[Stmt]) = this(label, Block.nextName, statements.toList, List(), false)

  def prepend(statement: Stmt) = this.copy(statements = statement.setLine((this.name, 1)) +: statements.map(stmt => stmt.incLine))

  override def toString: String =
    name + "(" + label + "): [" + children
      .map(b => b.name)
      .mkString(", ") + "] {\n" + statements.mkString(";\n") + "\n}"
}

object Block {
  def empty: Block = Block("empty", "?", Nil, Nil, false)

  private var currName = 'A'
  def nextName = {
    currName = (currName + 1).toChar
    currName.toString
  }

  def resetNames = {
    currName = 'A'
  }

  def apply(label: String, statements: List[Stmt], children: List[Block], atomic: Boolean = false) = {
    val name = Block.nextName
    new Block(label, name, statements.zip(statements.indices).map { case (stmt, i) => stmt.setLine((name, i + 1)) }, children, atomic)
  }

}

case class Assignment(lhs: Expression, expression: Expression, line: (String, Int)) extends Stmt(line) {
  def this(lhs: String, expression: Expression) =
    this(new Id(lhs, TInt, false, false, false, false), expression, ("", -1))
  def this(lhs: Expression, expression: Expression) =
    this(lhs, expression, ("", -1))
  override def toString: String = lhs + " = " + expression

  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
}

object Assignment {
  def apply(lhs: Id, expression: Expression) = new Assignment(lhs, expression, ("", -1))
}

case class ArrayAssignment(lhs: IdAccess, expression: Expression, line: (String, Int)) extends Stmt(line) {
  def this(name: String, index: Expression, expression: Expression) =
    this(new IdAccess(new Id(name, TInt, false, false, false, false), index), expression, ("", -1))
  override def toString: String =
    lhs.ident + "[" + lhs.index + "]" + " = " + expression

  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
}

/*
case object Break extends Stmt(line) {
  def self = this
}

case object Continue extends Stmt(line) {
  def self = this
}

case class Return(expression: Option[Expression]) extends Stmt(line) {
  def this(expression: Expression) = this(Some(expression))
}

object Return extends (Option[Expression] => Return) {
  val none = Return(None)
}

case object Fence extends Stmt(line) {
  def self: Fence.type = this
}

case object ControlFence extends Stmt(line) {
  def self: ControlFence.type = this
}
 */

case class If(test: Expression, left: Block, right: Option[Block], line: (String, Int)) extends Stmt(line) {
  def this(test: Expression, left: Block) = this(test, left, None, ("", -1))
  def this(test: Expression, left: Block, right: Block) =
    this(test, left, Some(right), ("", -1))

  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
}

case class Guard(test: Expression, line: (String, Int)) extends Stmt(line) {
  override def toString: String = "guard " + test

  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
}

object Guard {
  def apply(test: Expression) = new Guard(test, ("", -1))
}

case class While(
    test: Expression,
    invariant: Expression,
    gamma: List[GammaMapping],
    body: Block,
    line: (String, Int)
) extends Stmt(line) {
  def this(test: Expression, body: Block) =
    this(test, Const._true, List(), body, ("", -1))
  def this(test: Expression, invariant: Expression, body: Block) =
    this(test, invariant, List(), body, ("", -1))
  def this(
      test: Expression,
      invariant: Expression,
      gamma: Array[GammaMapping],
      body: Block
  ) = this(test, invariant, gamma.toList, body, ("", -1))

  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
}

case class DoWhile(
    test: Expression,
    invariant: Expression,
    gamma: List[GammaMapping],
    body: Block,
    line: (String, Int)
) extends Stmt(line) {
  def this(test: Expression, invariant: Expression, body: Block) =
    this(test, invariant, List(), body, ("", -1))
  def this(
      test: Expression,
      invariant: Expression,
      gamma: Array[GammaMapping],
      body: Block
  ) = this(test, invariant, gamma.toList, body, ("", -1))

  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
}

case class Atomic(statements: List[Stmt], line: (String, Int)) extends Stmt(line) {
  override def toString: String = "<" + statements.mkString(",") + ">"

  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
}

object Atomic {
  def apply(statements: List[Stmt]) = new Atomic(statements, ("", -1))
}

case class Assume(expression: Expression, line: (String, Int)) extends Stmt(line) {
  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)

  override def toString = s"assume ${expression.toString}"
}

object Assume {
  def apply(expression: Expression) = new Assume(expression, ("", -1))
}

case class Assert(expression: Expression, line: (String, Int), checkStableR: Boolean) extends Stmt(line) {
  def this(expression: Expression) = this(expression, ("", -1), false)
  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
  override def toString = s"assert ${expression.toString}"
}

object Assert {
  def apply(expression: Expression, checkStableR: Boolean = false) = new Assert(expression, ("", -1), checkStableR)
}

case class Havoc(line: (String, Int)) extends Stmt(line) {
  def incLine = this.copy(line = line.copy(_2 = line._2 + 1))
  def setLine(line: (String, Int)) = this.copy(line = line)
  override def toString = "Havoc"
}

object Havoc {
  def apply() = new Havoc(("", -1))
}
