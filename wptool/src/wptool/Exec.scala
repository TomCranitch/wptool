package wptool

// TODO include gamma of i in gamma computations

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
        if (c.atomic) res.addQs(res.Qs.map(Q => PredInfo(stableR(Q.pred,state), c, "atomic stableR")))
        else res
      }), state), RG)
      _state
    case assume: Assume => evalWp(assume, state)
    case assert: Assert =>
      val _state = evalWp(assert, state)
      // TODO would adding assert.expression to Qs allow to check if its correct
      if (assert.checkStableR) _state.addQs(
        PredInfo (
          stableR(assert.expression, state),
          assert,
          "StableR"
        ),
        PredInfo (
          eval(assert.expression, state),
          assert,
          "Assert"
        )
      )
      else _state
    case havoc: Havoc =>
      // TODO should this resolve to true/false ??
      // TODO need to somehow remove stableR (as per paper) - lazy hack is to set a boolean flag in the preprocessor 
      val _state = checkVcs(state.Qs, state.debug) match {
        case Some(p) =>
          if (!state.silent) printFalseVcs(p)
          if (state.debug) println("error found at havoc")
          state.copy(error = true)
        case None => 
          if (state.debug) println("conditions verified")
          state
      }

      _state.copy(Qs = List(PredInfo(Const._true, Malformed, "intial havoc")))
    case guard: Guard =>
      // TODO handle havoc -> true
      val _state = evalWp(guard, state)
      if (RG) {
        val gamma = computeGamma(eval(guard.test, state).vars.toList, state)
        val stabR = stableR(gamma, state)
        _state.addQs(
          PredInfo(gamma, guard, "Gamma"),
          PredInfo(stabR, guard, "StableR")
        )
      } else {
        _state
      }
    case assign: Assignment =>
      // TODO should prob make preds a list and then just append if necessary 
      val globalPred = if (state.globals.contains(assign.lhs)) BinOp("=>", getL(assign.lhs, state), computeGamma(eval(assign.expression, state).vars.toList, state)) else Const._true
      val controlPred = if (state.controls.contains(assign.lhs)) {
        constructForall(state.controlledBy.getOrElse(assign.lhs, Set()).map(contr => {
          BinOp(
            "=>",
            getL(contr, state), // .subst(Map(assign.lhs.toVar(state) -> Left(eval(assign.expression, state)))),
            BinOp("||", eval(contr.toGamma, state), getL(contr, state))
          )
        }).toList)
      } else Const._true

      // TODO should we be using rImplies when RG is false
      // TODO audit when RG is actually being used
      val _state = evalWp(assign, state).addQs(
        PredInfo(rImplies(globalPred, state), assign, "Global"),
        PredInfo(rImplies(controlPred, state), assign, "Control")
      )

      if (RG) {
        val guarantee = guar(assign, state)

        _state.addQs(
          PredInfo(rImplies(guarantee, state), assign, "Guarantee")
        ).incPrimeIndicies
      } else {
        _state.incPrimeIndicies
      }
    case assign: ArrayAssignment =>
      val indexSub = Map[Variable, Expression](Id.indexId.toVar(state) -> assign.lhs.ident)
      val globalPred = if (state.globals.contains(assign.lhs.ident)) BinOp("=>", getL(assign, state), computeGamma(eval(assign.expression, state).vars.toList, state)) else Const._true
      val controlPred = if (state.controls.contains(assign.lhs.ident)) {
        constructForall(state.controlledBy.getOrElse(assign.lhs.ident, Set()).map(contr => {
          BinOp(
            "=>",
            // TODO subst ????
            // subst main var with var updated with store
            getL(contr, state),
            BinOp("||", eval(contr.toGamma, state), getL(contr, state))
          )
        }).toList)
      } else Const._true

      var gammaPred = computeGamma(eval(assign.lhs.index, state).vars.toList, state)

      val _state = evalWp(assign, state).addQs(
        PredInfo(rImplies(globalPred, state), assign, "Global"),
        PredInfo(rImplies(controlPred, state), assign, "Control"),
        PredInfo(rImplies(gammaPred, state), assign, "Index Gamma")
      )


      if (RG) {
        /* TODO
        val guarantee = guar(assign, state)

        _state.addQs(
          PredInfo(rImplies(guarantee, state), assign, "Guarantee")
        ).incPrimeIndicies
        */

        _state
      } else {
        _state.incPrimeIndicies
      }
    case stmt =>
      println(s"Unhandled statement(wpif exec): $stmt")
      state.incPrimeIndicies
  }

  def evalWp (stmt: Statement, state: State) = state.copy(Qs = state.Qs.map(Q => Q.copy(pred = wp(Q.pred, stmt, state))))

  def wp (Q: Expression, stmt: Statement, state: State): Expression = stmt match {
    case Assume(exp) => BinOp("=>", eval(exp, state), Q)
    case Guard(exp) => 
      val stabRB = stableR(exp, state)
      BinOp("&&", 
        BinOp("=>", BinOp("&&", eval(exp, state), stabRB), Q),
        BinOp("=>", PreOp("!", stabRB), eval(exp, state))
      )
    case Assert(exp, checkStableR) => BinOp("&&", eval(exp, state), Q)
    case havoc: Havoc => Q
    case assign: Assignment =>
      val rhsGamma = computeGamma(eval(assign.expression, state).vars.toList, state)
      Q.subst(Map((assign.lhs.toGamma.toVar(state) -> Left(rhsGamma)), (assign.lhs.toVar(state) -> Left(eval(assign.expression, state)))))
    case assign: ArrayAssignment =>
      val rhsGamma = computeGamma(eval(assign.expression, state).vars.toList, state)
      // TODO this doesnt account of the index
      // TODO this is using the index, instead subst with a var updated with a store
      
      Q.subst(Map((assign.lhs.ident.toGamma.toVar(state) -> Right((eval(assign.lhs.index, state), rhsGamma))), (assign.lhs.ident.toVar(state) -> Right(eval(assign.lhs.index, state), eval(assign.expression, state)))))
    case stmt =>
      println("Unhandled statement(wp exec): " + stmt)
      Q
  }

  def eval (expr: Expression, state: State): Expression = expr match {
    case id: Id => id.toVar(state)
    case id: IdAccess => id.toVar(state).copy(index = eval(id.index, state))
    case BinOp(op, arg1, arg2) => BinOp(op, eval(arg1, state), eval(arg2, state))
    case PreOp(op, arg) => PreOp(op, eval(arg, state))
    case _: Lit | _: Const | _: Var | _: VarAccess => expr
    case expr =>
      println(s"Unhandled expression(eval): [${expr.getClass()}] $expr")
      expr
  }

  def getRely (ids: Set[Id], state: State) = {
    // TODO!!!!: BinOp("=>", L.getOrElse(id, Const._false).subst(subst), id.toPrime.toGamma)
    // Not sure what this meant
    // think it was for globals
    //

    // TODO handle arrays....
    
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

  def getL (id: Id, state: State): Expression = 
    if (id == Id.tmpId) Const._true
    else eval(state.L.getOrElse(id, throw new Error("L not defined for " + id)), state)
  def getL (id: ArrayAssignment, state: State): Expression = getL(id.lhs.ident, state).subst(Map(Id.indexId.toVar(state) -> Left(eval(id.lhs.index, state))))
  def primed (p: Expression, state: State) = eval(p, state).subst(state.ids.map(id => id.toVar(state) -> Left(id.toPrime.toVar(state))).toMap)
  // TODO take havoc statements into account
  def stableR (p: Expression, state: State) = eval(BinOp("=>", BinOp("&&", getRely(p.ids, state), p), primed(p, state)), state)
  def rImplies (p: Expression, state: State) = eval(BinOp("=>", getRely(p.ids, state), primed(p, state)), state)
  

  def guar (a: Assignment, state: State) = {
      // TODO update to allow guarantee to talk about specific indices 
      val rhsGamma = computeGamma(eval(a.expression, state).vars.toList, state)
      val idsNoLHS = state.ids.filter(id => id != a.lhs)
      val subst = idsNoLHS.map(id => id.toPrime.toVar(state) -> Left(id.toVar(state))).toMap ++ idsNoLHS.map(id => id.toPrime.toGamma.toVar(state) -> Left(id.toGamma.toVar(state))).toMap

      eval(eval(eval(state.guar, state)
        .subst(Map(a.lhs.toPrime.toVar(state) -> Left(a.expression), a.lhs.toPrime.toGamma.toVar(state) -> Left(rhsGamma))), state)
        .subst(subst), state)
  }

  def guar (a: ArrayAssignment, state: State) = {
    // TODO
    val rhsGamma = computeGamma(eval(a.expression, state).vars.toList, state)
    // TODO not sure how to handle the second substitution
  }

  def computeGamma (vars: List[Variable], state: State): Expression = vars match {
    case v :: Nil => eval(BinOp("||", v.toGamma(state), getL(v.ident, state)), state) // Default to high
    case v :: rest => eval(BinOp("&&", computeGamma(List(v), state), computeGamma(rest, state)), state)
    case Nil => Const._true
  }

  def joinStates (states: List[State], state: State) = {
    val indicies = states.foldLeft(state.indicies) { (a, i) => 
      i.indicies.map{ case (k, v) => k -> math.max(v, a.getOrElse(k, -1)) }
    }

    val preds = states.map(s => {
      if (s.indicies == indicies) s.Qs
      else {
        val conds = s.indicies.filter{ case (id, int) => indicies.get(id) match {
          case Some(i) => i != int
          case None => true
        }}.map{ case (id, ind) => BinOp("==", Var(id, ind), Var(id, indicies.getOrElse(id, -1))) }.toList

        s.Qs.map(info => info.copy(pred = BinOp("=>", constructForall(conds), info.pred)))
      }
    }).flatten

    val error = states.foldLeft(state.error) { case (a, i) => if (a || i.error) true else false }

    state.copy(
      Qs = preds, indicies = indicies, error = error
    )
  }
  

}
