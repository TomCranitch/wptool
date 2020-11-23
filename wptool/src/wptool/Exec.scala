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
    case Assignment(lhs, rhs) =>
      // If not using passification
      val globalPred = BinOp("=>", Const._true, BinOp("=>", Helper.getL(lhs, state, eval), createGamma(lhs)))
      val controlPred = if (state.controls.contains(lhs)) {
        Helper.constructForall(state.controlledBy.getOrElse(lhs, Set()).map(contr =>
          BinOp(
            "=>",
            Helper.getL(contr, state, eval).subst(Map((lhs, rhs))),
            BinOp("||", Helper.getL(contr, state, eval), Helper.getL(contr, state, eval))
          )
        ).toList)
      } else {
        Const._true
      }
      
      state.copy(Q = BinOp("&&", BinOp("&&", globalPred, controlPred), state.Q))
    case ifStmt: If =>
      val left = BinOp("=>", ifStmt.test, exec(ifStmt.left, state).Q)
      // TODO right
      // val right = BinOp("=>", PreOp("!", ifStmt.test), )
      val condGamma = Helper.constructForall(ifStmt.test.ids.toList.map(createGamma))
      state.copy(Q = BinOp("&&", condGamma, BinOp("&&", left, Const._true)))
    case stmt =>
      println("Unhandled statement: " + stmt)
      state
  }

  def eval (expr: Expression, state: State): Expression = expr match {
    case BinOp(op, arg1, arg2) => BinOp(op, eval(arg1, state), eval(arg2, state))
    // TODO
    case _: Lit | _: Const | _: Id | _: Var => expr
    case expr =>
      println("Unhandled expression: " + expr)
      expr
  }

  def createGamma (id: Id): Id = Id("gamma_" + id.name)
}
