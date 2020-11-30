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
      // TODO check
      exec(atomic.statements, state)
    case block: Block =>
      exec(block.statements, state)
    case assign: Assignment =>
      val globalPred = if (state.globals.contains(assign.lhs)) BinOp("=>", getL(assign.lhs, state), computeGamma(assign.expression.ids.toList, state)) else Const._true
      val controlPred = if (state.controls.contains(assign.lhs)) {
        constructForall(state.controlledBy.getOrElse(assign.lhs, Set()).map(contr =>
          BinOp(
            "=>",
            getL(contr, state).subst(Map(assign.lhs -> assign.expression)),
            BinOp("||", GammaId(contr), getL(contr, state)) // TODO this is the issue !!
          )
        ).toList)
      } 
      else Const._true
      val PO = BinOp("&&", globalPred, controlPred)

      val rhsGamma = computeGamma(assign.expression.ids.toList, state)

      val Q = state.Q.subst(Map((assign.lhs.gamma -> rhsGamma), (assign.lhs -> assign.expression)))

      val guarantee = guar(assign, state)
      println(assign + ": " + guarantee)
      // println(stableR(guarantee, state))


      val pred = constructForall(List(PO, Q, guarantee))

      // state.copy(Q = BinOp("&&", pred, stableR(pred, state)))
      // state.copy(Q = BinOp("&&", pred, stableR(constructForall(List(PO, Q)), state)))
      state.copy(Q = pred)

    case ifStmt: If =>
      val state1 = exec(ifStmt.left, state)
      val state2 = exec(ifStmt.right.get, state) // Right should contain block from passification
      val left = BinOp("=>", ifStmt.test, state1.Q)
      val right = BinOp("=>", PreOp("!", ifStmt.test), state2.Q)
      val condGamma = computeGamma(ifStmt.test.ids.toList, state)
      // TODO is this pred correct
      val condStableR = BinOp("=>", PreOp("!", stableR(ifStmt.test, state)), BinOp("&&", state1.Q, state2.Q))

      // TODO include Q??
      state.copy(Q = constructForall(List(condGamma, stableR(condGamma, state), left, right, condStableR)))

    case loop: While => 
      val gammaPred = constructForall(loop.gamma.map(x => BinOp("==", GammaId(x.variable), x.security.toTruth)))
      val inv = BinOp("&&", gammaPred, loop.invariant)
      val condGamma = computeGamma(loop.test.ids.toList, state)
      val PO = BinOp("&&", eval(inv, state), BinOp("=>", eval(inv, state), condGamma))
      // TODO i dont think this considers forall sigma
      val body = exec(loop.body, state.copy(Q=eval(inv, state)))
      val wpQ = BinOp("&&", BinOp("=>", BinOp("&&", eval(inv, state), eval(loop.test, state)), body.Q), BinOp("=>", BinOp("&&", eval(inv, state), PreOp("!", eval(loop.test, state))), state.Q))
      state.copy(Q = constructForall(List(PO, stableR(inv, state), wpQ)))

    case cas: CompareAndSwap =>
      val gamma = computeGamma(cas.e1.ids.toList, state)
      val state1 = exec(Assignment(cas.x, cas.e2), exec(Assignment(cas.result, Lit(1)), state))
      val state2 = exec(Assignment(cas.x, Lit(0)), state)
      val guarantee = guar(Assignment(cas.x, cas.e2), state)
      val left = BinOp("=>", BinOp("==", cas.x, cas.e1), BinOp("&&", guarantee, state1.Q))
      val right = BinOp("=>", BinOp("==", cas.x, cas.e1), state2.Q)
      val pred = constructForall(List(left, right, gamma))
      state.copy(Q = BinOp("&&", pred, stableR(pred, state)))
    case stmt =>
      println("Unhandled statement: " + stmt)
      state
  }

  def eval (expr: Expression, state: State): Expression = expr match {
    case BinOp(op, arg1, arg2) => BinOp(op, eval(arg1, state), eval(arg2, state))
    case _: Lit | _: Const | _: Id | _: GammaId  => expr
    case expr =>
      println("Unhandled expression: " + expr)
      expr
  }

  def computeGamma (ids: List[Id], state: State): Expression = ids match {
    case i :: Nil => BinOp("||", GammaId(i), state.L.getOrElse(i, Const._false)) // Default to high
    case i :: rest => BinOp("&&", computeGamma(List(i), state), computeGamma(rest, state))
    case Nil => Const._true
  }

  def getL (id: Id, state: State): Expression = eval(state.L.getOrElse(id, throw new Error("L not defined for " + id)), state)
  
  def constructForall (exprs: List[Expression]): Expression = exprs match {
    case expr :: Nil => expr
    case expr :: rest =>
      BinOp("&&", expr, constructForall(rest))
    case Nil => Const._true
  }

  def stableR (p: Expression, state: State) = {
    val primed = p.subst(state.ids.map(id => id -> id.prime).toMap)
    BinOp("=>", BinOp("&&", state.rely, p), primed)
  }

  def guar (a: Assignment, state: State) = {
      // TODO detect x ~ y
      val rhsGamma = computeGamma(a.expression.ids.toList, state)
      val idsNoLHS = state.ids.filter(id => id != a.lhs)
      val subst: Map[Identifier, Expression] = idsNoLHS.map(id => id.prime -> id).toMap[Identifier, Expression] ++ idsNoLHS.map(id => id.prime.gamma -> id.gamma).toMap[Identifier, Expression]
      state.guar
        .subst(Map(a.lhs.prime -> a.expression, a.lhs.prime.gamma -> rhsGamma))
        .subst(subst)
  }
}
