package wptool

object Exec {
  @scala.annotation.tailrec
  def exec(statements: List[Statement], state: State): State = statements match {
    case rest :+ last =>
      val _state = exec(last, state)
      exec(rest, _state)
    case Nil => state
  }

  def exec (stmt: Statement, state: State): State = stmt match {
    case atomic: Atomic =>
      exec(atomic.statements, state)
    case block: Block =>
      exec(block.statements, state)
    case assume: Assume =>
      state.copy(Q = BinOp("=>", eval(assume.expression, state), state.Q))
    case assert: Assert =>
      state.copy(Q = BinOp("&&", eval(assert.expression, state), state.Q))
    case ifStmt: If =>
      val state1 = exec(ifStmt.left, state)
      val state2 = exec(ifStmt.right.get, state) // Right should contain block from passification
      val left = BinOp("=>", ifStmt.test, state1.Q)
      val right = BinOp("=>", PreOp("!", ifStmt.test), state2.Q)
      // println(Gamma(ifStmt.test.variables).eval(state))
      val gamma = ifStmt.test.variables.map(vari => vari.gamma).max.toTruth
      println(ifStmt.test.variables + " - " + ifStmt.test.variables.map(vari => vari.gamma) + ": " + gamma)
      state.copy(Q = BinOp("&&", gamma, BinOp("&&", left, right)))
    case stmt =>
      println("Unhandled statement: " + stmt)
      state
  }

  def eval (expr: Expression, state: State): Expression = expr match {
    case BinOp(op, arg1, arg2) => BinOp(op, eval(arg1, state), eval(arg2, state))
    case _: Lit | _: Const | _: Id | _: Var => expr
    case expr =>
      println("Unhandled expression: " + expr)
      expr
  }

}
