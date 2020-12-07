package wptool

object Exec {
  @scala.annotation.tailrec
  def exec(statements: List[Statement], state: State): State = statements match {
    case rest :+ last =>
      val _state = exec(last, state)
      exec(rest, _state)
    case Nil => state
  }

  def exec (stmt: Statement, state: State, RG: Boolean = true): State = stmt match {
    case block: Block =>
      // TODO do we need to join over the primeIndicies (i think we do)
      exec(block.statements, state.copy(
        Q = constructForall(block.children.map(c => exec(c, state).Q)
      )))
    case assume: Assume =>
      state.copy(Q = eval(BinOp("=>", assume.expression, state.Q), state))
    case Assert(exp, checkStableR) =>
      if (checkStableR) state.copy(Q = constructForall(List(exp, state.Q, stableR(exp, state))))
      else state.copy(Q = BinOp("&&", exp, state.Q))
    case havoc: Havoc =>
      // TODO replace variables with fresh variables (wp(havoc x, Q) = Q[x -> x.fresh])
      // Q.subst(Q.ids.fresh)
      // TODO should this resolve to true/false ??
      // TODO need to somehow remove stableR (as per paper) - lazy hack is to set a boolean flag in the preprocessor 
      state.incNonPrimeIndicies
    // Ignore
    case Guard(test: Expression) =>
      // TODO
      // TODO handle havoc -> true
      val gamma = computeGamma(eval(test, state).vars.toList, state)
      val stabR = stableR(gamma, state)
      val stabRB = stableR(test, state)
      state.copy(Q = eval(constructForall(List(gamma, stabR, BinOp("=>", BinOp("&&", stabRB, test), state.Q), BinOp("=>", PreOp("!", stabRB), state.Q))), state))
    case assign: Assignment =>
      val globalPred = if (state.globals.contains(assign.lhs)) BinOp("=>", getL(assign.lhs, state), computeGamma(eval(assign.expression, state).vars.toList, state)) else Const._true
      val controlPred = if (state.controls.contains(assign.lhs)) {
        constructForall(state.controlledBy.getOrElse(assign.lhs, Set()).map(contr =>
          BinOp(
            "=>",
            getL(contr, state).subst(Map(assign.lhs.toVar(state) -> assign.expression)),
            BinOp("||", contr.toGamma, getL(contr, state))
          )
        ).toList)
      } 
      else Const._true
      val PO = BinOp("&&", globalPred, controlPred)

      val rhsGamma = computeGamma(eval(assign.expression, state).vars.toList, state)

      val Q = state.Q.subst(Map((assign.lhs.toGamma.toVar(state) -> rhsGamma), (assign.lhs.toVar(state) -> assign.expression)))


      if (RG) {
        val guarantee = guar(assign, state)
        val pred = constructForall(List(PO, Q, guarantee))

        //state.copy(Q = BinOp("&&", guarantee, rImplies(pred, state))).incPrimeIndicies
        state.copy(Q = rImplies(pred, state)).incPrimeIndicies
      } else {
        state.copy(Q = eval(BinOp("&&", PO, Q), state)).incPrimeIndicies
      }
    case stmt =>
      println("Unhandled statement(exec): " + stmt)
      state.incPrimeIndicies
  }

  def eval (expr: Expression, state: State): Expression = expr match {
    case id: Id => id.toVar(state)
    case BinOp(op, arg1, arg2) => BinOp(op, eval(arg1, state), eval(arg2, state))
    case PreOp(op, arg) => PreOp(op, eval(arg, state))
    case _: Lit | _: Const | _: Var => expr
    // case _: CompareAndSwap => throw new Error("Unexpected compare and swap")
    case expr =>
      println("Unhandled expression: " + expr)
      expr
  }


  def getL (id: Id, state: State): Expression = eval(state.L.getOrElse(id, throw new Error("L not defined for " + id)), state)
  def primed (p: Expression, state: State) = eval(p, state).subst(state.ids.map(id => id.toVar(state) -> id.toPrime.toVar(state)).toMap)
  // TODO maybe only use relevant parts of the axioms
  // TODO take havoc statements into account
  def stableR (p: Expression, state: State) = eval(BinOp("=>", BinOp("&&", state.rely, p), primed(p, state)), state)
  def rImplies (p: Expression, state: State) = eval(BinOp("=>", state.rely, primed(p, state)), state)

  def guar (a: Assignment, state: State) = {
      // TODO detect x ~ y
      val rhsGamma = computeGamma(eval(a.expression, state).vars.toList, state)
      val idsNoLHS = state.ids.filter(id => id != a.lhs)
      val subst = idsNoLHS.map(id => id.toPrime.toVar(state) -> id).toMap[Var, Expression] ++ idsNoLHS.map(id => id.toPrime.toGamma.toVar(state) -> id.toGamma.toVar(state)).toMap[Var, Expression]
      eval(state.guar, state)
        .subst(Map(a.lhs.toPrime.toVar(state) -> a.expression, a.lhs.toPrime.toGamma.toVar(state) -> rhsGamma))
        .subst(subst)
  }

  def computeGamma (vars: List[Var], state: State): Expression = vars match {
    case v :: Nil => eval(BinOp("||", v.toGamma, state.L.getOrElse(v.ident, Const._false)), state) // Default to high
    case v :: rest => eval(BinOp("&&", computeGamma(List(v), state), computeGamma(rest, state)), state)
    case Nil => Const._true
  }

  

}
