package wptool

// TODO i dont think prime variables are getting incremented often enough

object Exec {
  @scala.annotation.tailrec
  def exec(statements: List[Statement], state: State, RG: Boolean = true): State = statements match {
    case rest :+ last =>
      val _state = exec(last, state, RG)
      exec(rest, _state, RG)
    case Nil => state
  }

  def exec (block: Block, state: State): State = exec(block, state, !block.atomic)

  def exec (stmt: Statement, state: State, RG: Boolean): State = stmt match {
    case block: Block =>
      val _state = exec(block.statements, joinStates(block.children.map(c => {
        val res = exec(c, state)
        if (c.atomic) res.copy(Q = BinOp("&&", stableR(res.Q, state), res.Q))
        else res
      }), state), RG)
      _state
    case assume: Assume =>
      state.copy(Q = eval(BinOp("=>", eval(assume.expression, state), state.Q), state))
    case Assert(exp, checkStableR) =>
      if (checkStableR) state.copy(Q = constructForall(List(eval(exp, state), state.Q, stableR(exp, state))))
      else state.copy(Q = BinOp("&&", eval(exp, state), state.Q))
    case havoc: Havoc =>
      // TODO should this resolve to true/false ??
      // TODO need to somehow remove stableR (as per paper) - lazy hack is to set a boolean flag in the preprocessor 
      // TODO: this fails in the case of nested loops (or more specifically the join operation does)
      state.incNonPrimeIndicies
      // state
    case Guard(test: Expression) =>
      // TODO handle havoc -> true
      if (RG) {
        val gamma = computeGamma(eval(test, state).vars.toList, state)
        val stabR = stableR(gamma, state)
        val stabRB = stableR(test, state)
        state.copy(Q = eval(constructForall(List(gamma, stabR, BinOp("=>", BinOp("&&", stabRB, test), state.Q), BinOp("=>", PreOp("!", stabRB), state.Q))), state))
      } else {
        state.copy(Q = eval(BinOp("=>", test, state.Q), state))
      }
    case assign: Assignment =>
      val globalPred = if (state.globals.contains(assign.lhs)) BinOp("=>", getL(assign.lhs, state), computeGamma(eval(assign.expression, state).vars.toList, state)) else Const._true
      val controlPred = if (state.controls.contains(assign.lhs)) {
        constructForall(state.controlledBy.getOrElse(assign.lhs, Set()).map(contr =>
          BinOp(
            "=>",
            getL(contr, state).subst(Map(assign.lhs.toVar(state) -> assign.expression)),
            BinOp("||", eval(contr.toGamma, state), getL(contr, state))
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
    case expr =>
      println("Unhandled expression: " + expr)
      expr
  }

  def getRely (ids: Set[Id], state: State) = {
    // TODO!!!!: BinOp("=>", L.getOrElse(id, Const._false).subst(subst), id.toPrime.toGamma)
    // Not sure what this meant
    // think it was for globals
    
    eval(constructForall(ids.toList.map(i => 
        if (state.globals.contains(i)) {
          BinOp("=>", BinOp("==", i, i.toPrime), BinOp("==", i.toGamma, i.toPrime.toGamma))
        } else {
          BinOp(
            "&&", 
            BinOp("==", i, i.toPrime), 
            BinOp("==", i.toGamma, i.toPrime.toGamma)
          )
        }
      ) :+ state.rely), state)
  }

  def getL (id: Id, state: State): Expression = eval(state.L.getOrElse(id, throw new Error("L not defined for " + id)), state)
  def primed (p: Expression, state: State) = eval(p, state).subst(state.ids.map(id => id.toVar(state) -> id.toPrime.toVar(state)).toMap)
  // TODO take havoc statements into account
  def stableR (p: Expression, state: State) = eval(BinOp("=>", BinOp("&&", getRely(p.ids, state), p), primed(p, state)), state)
  def rImplies (p: Expression, state: State) = eval(BinOp("=>", getRely(p.ids, state), primed(p, state)), state)
  

  def guar (a: Assignment, state: State) = {
      // TODO detect x ~ y
      val rhsGamma = computeGamma(eval(a.expression, state).vars.toList, state)
      val idsNoLHS = state.ids.filter(id => id != a.lhs)
      val subst = idsNoLHS.map(id => id.toPrime.toVar(state) -> id).toMap[Var, Expression] ++ idsNoLHS.map(id => id.toPrime.toGamma.toVar(state) -> id.toGamma.toVar(state)).toMap[Var, Expression]

      eval(eval(state.guar, state)
        .subst(Map(a.lhs.toPrime.toVar(state) -> a.expression, a.lhs.toPrime.toGamma.toVar(state) -> rhsGamma)), state)
        .subst(subst)
  }

  def computeGamma (vars: List[Var], state: State): Expression = vars match {
    case v :: Nil => eval(BinOp("||", v.toGamma(state), state.L.getOrElse(v.ident, Const._false)), state) // Default to high
    case v :: rest => eval(BinOp("&&", computeGamma(List(v), state), computeGamma(rest, state)), state)
    case Nil => Const._true
  }

  def joinStates (states: List[State], state: State) = {
    val indicies = states.foldLeft(state.indicies) { (a, i) => 
      i.indicies.map{ case (k, v) => k -> math.max(v, a.getOrElse(k, -1)) }
    }

    val preds = states.map(s => {
      if (s.indicies == indicies) s.Q
      else {
        val conds = s.indicies.filter{ case (id, int) => indicies.get(id) match {
          case Some(i) => i != int
          case None => true
        }}.map{ case (id, ind) => BinOp("==", Var(id, ind), Var(id, indicies.getOrElse(id, -1))) }.toList

        BinOp("=>", constructForall(conds), s.Q)
      }
    })

    state.copy(
      Q = constructForall(preds), indicies = indicies
    )
  }
  

}
