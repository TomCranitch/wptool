package wptool

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
      val _state = checkVcs(state.Qs, state.debug, state.simplify) match {
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
      val globalPred = if (state.globals.contains(assign.lhs)) BinOp("=>", getL(assign.lhs, state), computeGamma(eval(assign.expression, state).vars.toList, state)) else Const._true
      val controlPred = if (state.controls.contains(assign.lhs)) {
        constructForall(state.controlledBy.getOrElse(assign.lhs, Set()).map(contr => {
          BinOp(
            "=>",
            getL(contr, state),
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
            getL(contr, state),
            BinOp("||", eval(contr.toGamma, state), getL(contr, state))
          )
        }).toList)
      } else Const._true

      var gammaPred = computeGamma(eval(assign.lhs.index, state).vars.toList, state)

      val _state = evalWp(assign, state).addQs(
        PredInfo(rImplies(globalPred, assign.lhs.index, state), assign, "Global"),
        PredInfo(rImplies(controlPred, assign.lhs.index, state), assign, "Control"),
        PredInfo(rImplies(gammaPred, assign.lhs.index, state), assign, "Index Gamma")
      )


      if (RG) {
        val guarantee = guar(assign, state)

        _state.addQs(
          PredInfo(rImplies(guarantee, assign.lhs.index, state), assign, "Guarantee")
        ).incPrimeIndicies
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
    case Assert(exp, checkStableR) => BinOp("&&", eval(exp, state), Q) // Potentially move to exec to evaluate separately
    case havoc: Havoc => Q
    case assign: Assignment =>
      val rhsGamma = computeGamma(eval(assign.expression, state).vars.toList, state)
      Q.subst(Map((assign.lhs.toGamma.toVar(state) -> Left(rhsGamma)), (assign.lhs.toVar(state) -> Left(eval(assign.expression, state)))))
    case assign: ArrayAssignment =>
      val rhsGamma = computeGamma(eval(assign.expression, state).vars.toList, state)
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
    case s: VarStore => s.copy(array = eval(s.array, state), index = eval(s.index, state), exp = eval(s.exp, state))
    case a: VarAccess => a.copy(index = eval(a.index, state))
    case forall: ForAll => forall.copy( bound = forall.bound.map(b => eval(b, state)), body = eval(forall.body, state) )
    case _: Lit | _: Const | _: Var => expr
    case expr =>
      println(s"Unhandled expression(eval): [${expr.getClass()}] $expr")
      expr
  }

  def getRely (exp: Expression, state: State) = eval(BinOp("&&", getRelyRec(eval(exp, state), state).getOrElse(Const._true), eval(state.rely, state)), state)

  // TODO: remove vars that have already been added
  // this cant be done for arrays (with different indicies)
  // TODO could this be similified by just looking at exp.vars
  def getRelyRec (exp: Expression, state: State): Option[Expression] = exp match {
    case BinOp(op, arg1, arg2) => Some(constructForallOpt(getRelyRec(arg1, state), getRelyRec(arg2, state)))
    case PreOp(op, arg) => getRelyRec(arg, state)
    case v: Var => 
      if (state.globals.contains(v.ident)) {
        Some(BinOp("=>", BinOp("==", v, v.toPrime(state)), BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state))))
      } else {
        Some(BinOp(
          "&&", 
          BinOp("==", v, v.toPrime(state)), 
          BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state))
        ))
      }
    case v: VarAccess =>
      val pred = if (state.globals.contains(v.ident)) {
        BinOp("=>", BinOp("==", v, v.toPrime(state)), BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state)))
      } else {
        BinOp(
          "&&", 
          BinOp("==", v, v.toPrime(state)), 
          BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state))
        )
      }

      Some(BinOp("&&", pred, eval(state.arrRelys.getOrElse(v.ident, Const._true), state).subst(Map(Id.indexId.toVar(state) -> Left(eval(v.index, state))))))
    case s: VarStore => getRelyRec(s.exp, state) // TODO do we need it for arr and index as well? (similarly for eval)
    case _: Lit | _: Const => None
    case expr =>
      println(s"Unhandled expression(getRely): [${expr.getClass()}] $expr")
      None
  }

  def getL (id: Id, state: State): Expression = 
    if (id == Id.tmpId) Const._true
    else eval(state.L.getOrElse(id, throw new Error("L not defined for " + id)), state)
  def getL (id: ArrayAssignment, state: State): Expression = getL(id.lhs.ident, state).subst(Map(Id.indexId.toVar(state) -> Left(eval(id.lhs.index, state))))
  def primed (p: Expression, state: State) = eval(p, state).subst(state.ids.map(id => id.toVar(state) -> Left(id.toPrime.toVar(state))).toMap)
  // TODO take havoc statements into account
  def stableR (p: Expression, state: State) = eval(BinOp("=>", BinOp("&&", getRely(p, state), p), primed(p, state)), state)
  def rImplies (p: Expression, state: State) = eval(BinOp("=>", getRely(p, state), primed(p, state)), state)
  def stableR (p: Expression, index: Expression, state: State) = eval(BinOp("=>", BinOp("&&", getRely(p, state).subst(Map(Id.indexId.toVar(state) -> Left(index))), p), primed(p, state)), state)
  def rImplies (p: Expression, index: Expression, state: State) = eval(BinOp("=>", getRely(p, state).subst(Map(Id.indexId.toVar(state) -> Left(index))), primed(p, state)), state)
  

  // TODO also need to handle arrays on RHS
  def guar (a: Assignment, state: State) = {
      // TODO update to allow guarantee to talk about specific indices 
      val rhsGamma = computeGamma(eval(a.expression, state).vars.toList, state)
      val idsNoLHS = state.ids.filter(id => id != a.lhs)
      val subst = idsNoLHS.map(id => id.toPrime.toVar(state) -> Left(id.toVar(state))).toMap ++ idsNoLHS.map(id => id.toPrime.toGamma.toVar(state) -> Left(id.toGamma.toVar(state))).toMap

      eval(eval(eval(state.guar, state)
        .subst(Map(a.lhs.toPrime.toVar(state) -> Left(a.expression), a.lhs.toPrime.toGamma.toVar(state) -> Left(rhsGamma))), state)
        .subst(subst), state)
  }

  // TODO fix subst when multiple arrays present (does this really matter tho or is it handled automatically)
  def guar (a: ArrayAssignment, state: State) = {
    val rhsGamma = computeGamma(eval(a.expression, state).vars.toList, state)
    val idsNoLHS = state.ids.filter(id => id != a.lhs.ident)
    // TODO not sure how to handle the second substitution
    val subst = idsNoLHS.map(id => id.toPrime.toVar(state) -> Left(id.toVar(state))).toMap ++ idsNoLHS.map(id => id.toPrime.toGamma.toVar(state) -> Left(id.toGamma.toVar(state))).toMap
    
    eval(eval(BinOp("&&", eval(state.guar, state), eval(state.arrGuars.getOrElse(a.lhs.ident, Const._true), state).subst(Map(Id.indexId.toVar(state) -> Left(eval(a.lhs.index, state)))))
      .subst(Map(a.lhs.ident.toPrime.toVar(state) -> Right(a.lhs.index, a.expression), a.lhs.ident.toPrime.toGamma.toVar(state) -> Right(a.lhs.index, rhsGamma))), state)
      .subst(subst), state)
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
