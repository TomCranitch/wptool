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
    /*
    case VarAssignment(lhs, rhs) =>
      // If not using passification
      val globalPred = BinOp("=>", Const._true, BinOp("=>", lhs.L, lhs.gamma))
      val controlPred = if (state.controls.contains(lhs.ident)) {
        Helper.constructForall(state.controlledBy.getOrElse(lhs.ident, Set()).map(contr =>
          BinOp(
            "=>",
            Helper.getL(contr, state, eval).subst(Map((lhs.ident, rhs))),
            BinOp("||", Helper.getL(contr, state, eval), Helper.getL(contr, state, eval))
          )
        ).toList)
      } else {
        Const._true
      }
      
      state.copy(Q = BinOp("&&", BinOp("&&", globalPred, controlPred), state.Q))
     */
    case ifStmt: If =>
      val state1 = exec(ifStmt.left, state)
      val state2 = exec(ifStmt.right.get, state) // Right should contain block from passification
      val left = BinOp("=>", ifStmt.test, state1.Q)
      val right = BinOp("=>", PreOp("!", ifStmt.test), state2.Q)
      // println(Gamma(ifStmt.test.variables).eval(state))
      val condGamma = computeGamma(ifStmt.test.variables.toList)
      // TODO include Q??
      state.copy(Q = BinOp("&&", condGamma, BinOp("&&", left, right)))
    case loop: While => 
      val condGamma = computeGamma(loop.test.variables.toList)
      val PO = BinOp("&&", eval(loop.invariant, state), BinOp("=>", eval(loop.invariant, state), condGamma))
      val body = exec(loop.body, state)
      val wpQ = BinOp("&&", BinOp("=>", BinOp("&&", eval(loop.invariant, state), eval(loop.test, state)), eval(loop.invariant, state)), BinOp("=>", BinOp("&&", eval(loop.invariant, state), PreOp("!", eval(loop.test, state))), state.Q))
      println(PO)
      state.copy(Q = BinOp("&&", PO, wpQ))
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

  def computeGamma (variables: List[Var]): Expression = variables match {
    case v :: Nil => BinOp("||", v.gamma, v.L)
    case v :: rest => BinOp("&&", computeGamma(List(v)), computeGamma(rest))
    case Nil => Const._true
  }

}
