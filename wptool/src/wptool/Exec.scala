package wptool

object Exec {
  @scala.annotation.tailrec
  def exec(
      statements: List[Stmt],
      state: State,
      RG: Boolean = true
  ): State = statements match {
    case rest :+ last =>
      val _state = exec(last, state, RG)
      exec(rest, _state, RG)
    case Nil => state
  }

  def exec(block: Block, state: State): State =
    exec(block, state, !block.atomic)

  def exec(block: Block, state: State, RG: Boolean): State = {
    val _state = exec(
      block.statements,
      joinStates(
        block.children.map(c => {
          val res = exec(c, state)
          if (c.atomic)
            // TODO change this to R implies
            res.copy(Qs = res.Qs.map(q => q.copy(pred = rImplies(q.pred, state))))
          else res
        }),
        state,
        block.name
      ),
      RG
    )
    _state
  }

  def exec(stmt: Stmt, state: State, RG: Boolean): State = stmt match {
    case assume: Assume => evalWp(assume, state, RG).incPrimeIndicies
    case assert: Assert =>
      val _state = evalWp(assert, state, RG)
      if (assert.checkStableR)
        _state
          .addQs(
            new PredInfo(
              stableR(assert.expression, state),
              assert,
              "Assert"
            )
          )
          .incPrimeIndicies
      else
        _state
          .addQs(
            new PredInfo(
              eval(assert.expression, state, true),
              assert,
              "Assert"
            )
          )
          .incPrimeIndicies
    case havoc: Havoc =>
      val _state = checkVcs(state.Qs, state.debug, state.simplify) match {
        case Some(p) =>
          if (!state.silent) printFalseVcs(p)
          if (state.debug) println("error found at havoc")
          state.copy(error = true).incPrimeIndicies
        case None =>
          if (state.debug) println("conditions verified")
          state.incPrimeIndicies
      }

      _state.copy(Qs = List(new PredInfo(Const._true, EmptyStmt, "initial havoc")))
    case guard: Guard =>
      val _state = evalWp(guard, state, RG)
      if (RG) {
        val gamma = computeGamma(guard.test, state)
        val stabR = stableR(gamma, state)
        _state
          .addQs(
            new PredInfo(gamma, guard, "Gamma"),
            new PredInfo(stabR, guard, "StableR")
          )
          .incPrimeIndicies
      } else {
        _state.incPrimeIndicies
      }
    case assign: Assignment =>
      val globalPred =
        if (state.globals.contains(assign.lhs))
          BinOp.pred(
            "=>",
            getL(assign.lhs, state),
            computeGamma(assign.expression, state)
          )
        else Const._true
      val controlPred = if (state.controls.contains(assign.lhs)) {
        constructForall(
          state.controlledBy
            .getOrElse(assign.lhs, Set())
            .map(contr => {
              BinOp.pred(
                "=>",
                eval(getL(contr, state).subst(Map(assign.lhs.toVar(state) -> Left(assign.expression))), state, true), // TODO
                BinOp.pred("||", eval(contr.toGamma, state, true), getL(contr, state))
              )
            })
            .toList
        )
      } else Const._true

      val _state = evalWp(assign, state, RG)

      if (RG) {
        val guarantee = guar(assign, state)

        _state
          .addQs(
            new PredInfo(rImplies(guarantee, state), assign, "Guarantee"),
            new PredInfo(rImplies(globalPred, state), assign, "Global"),
            new PredInfo(rImplies(controlPred, state), assign, "Control")
          )
          .incPrimeIndicies
      } else {
        _state
          .addQs(
            new PredInfo(globalPred, assign, "Global"),
            new PredInfo(controlPred, assign, "Control")
          )
          .incPrimeIndicies
      }
    case assign: ArrayAssignment =>
      val indexSub =
        Map(Id.indexId.toVar(state) -> assign.lhs.ident)
      val globalPred =
        if (state.globals.contains(assign.lhs.ident))
          BinOp.pred(
            "=>",
            getL(assign.lhs, state),
            computeGamma(assign.expression, state)
          )
        else Const._true
      val controlPred = if (state.controls.contains(assign.lhs.ident)) {
        constructForall(
          state.controlledBy
            .getOrElse(assign.lhs.ident, Set())
            .map(contr => {
              BinOp.pred(
                "=>",
                eval(
                  getL(contr, state).subst(Map(assign.lhs.ident.toVar(state) -> Right((assign.lhs.index, assign.expression)))),
                  state,
                  true
                ), // TODO
                BinOp.pred(
                  "||",
                  eval(contr.toGamma, state, true),
                  getL(contr, state).subst(Map(Id.indexId.toVar(state) -> Left(assign.lhs.index)))
                ) // TODO check subst is correct
              )
            })
            .toList
        )
      } else Const._true
      var gammaPred = computeGamma(assign.lhs.index, state)

      val _state = evalWp(assign, state, RG)

      if (RG) {
        val guarantee = guar(assign, state)

        _state
          .addQs(
            new PredInfo(
              rImplies(guarantee, assign.lhs.index, state),
              assign,
              "Guarantee"
            ),
            new PredInfo(
              rImplies(globalPred, assign.lhs.index, state),
              assign,
              "Global"
            ),
            new PredInfo(
              rImplies(controlPred, assign.lhs.index, state),
              assign,
              "Control"
            ),
            new PredInfo(
              rImplies(gammaPred, assign.lhs.index, state),
              assign,
              "Index Gamma"
            )
          )
          .incPrimeIndicies
      } else {
        _state
          .addQs(
            new PredInfo(globalPred, assign, "Global"),
            new PredInfo(controlPred, assign, "Control"),
            new PredInfo(gammaPred, assign, "Index Gamma")
          )
          .incPrimeIndicies
      }
    case stmt =>
      println(s"Unhandled statement(wpif exec): $stmt")
      state.incPrimeIndicies
  }

  def evalWp(stmt: Stmt, state: State, RG: Boolean) = {
    if (RG) state.copy(Qs = state.Qs.map(Q => Q.copy(pred = rImplies(wp(Q.pred, stmt, state), state))))
    else state.copy(Qs = state.Qs.map(Q => Q.copy(pred = wp(Q.pred, stmt, state))))
  }

  def wp(Q: Expression, stmt: Stmt, state: State): Expression = {
    stmt match {
      case Assume(exp, _) => BinOp.pred("=>", eval(exp, state, true), Q)
      case Guard(exp, _) =>
        val stabRB = stableR(exp, state)
        BinOp.pred(
          "&&",
          BinOp.pred("=>", BinOp.pred("&&", eval(exp, state, true), stabRB), Q),
          BinOp.pred("=>", PreOp("!", Type.TBool, Type.TBool, stabRB), eval(exp, state, true))
        )
      case Assert(exp, checkStableR, _) =>
        Q
      case havoc: Havoc => Q
      case ass: Assignment =>
        val assign = ass.asInstanceOf[Assignment]
        val rhsGamma = computeGamma(assign.expression, state)

        Q.subst(
          Map(
            (assign.lhs.toGamma.toVar(state) -> Left(rhsGamma)), // TODO should gamma be an array (i think so)
            // (assign.lhs.toVar(state) -> Left(eval(assign.expression, state)))
            ((if (ass.lhs.prime) Id.memId.toPrime.toVar(state) else Id.memId.toVar(state))
              -> Right(
                (
                  Id.getAddr(ass.lhs, state),
                  eval(ass.expression, state, true)
                )
              ))
          )
        )
      case ass: ArrayAssignment =>
        val assign = ass.asInstanceOf[ArrayAssignment]
        val rhsGamma = computeGamma(assign.expression, state)

        Q.subst(
          Map(
            (assign.lhs.ident.toGamma.toVar(state) -> Right(
              (eval(assign.lhs.index, state, true), rhsGamma)
            )),
            (assign.lhs.ident.toVar(state) -> Right(
              eval(assign.lhs.index, state, true),
              eval(assign.expression, state, true)
            ))
          )
        )
      case stmt =>
        println("Unhandled statement(wp exec): " + stmt)
        Q
    }
  }

  def eval(expr: Expression, state: State, memAccess: Boolean): Expression = expr match {
    case id: Id =>
      if (id == Id.indexId) id.toVar(state)
      else if (memAccess && !id.gamma)
        VarAccess(if (id.prime) Id.memId.toPrime.toVar(state) else Id.memId.toVar(state), Id.getAddr(id, state))
      else id.toVar(state)
    case v: Var =>
      if (v.ident == Id.indexId) v
      else if (memAccess && !v.ident.gamma)
        VarAccess(if (v.ident.prime) Id.memId.toPrime.toVar(state) else Id.memId.toVar(state), Id.getAddr(v.ident, state))
      else if (memAccess && !v.ident.gamma)
        VarAccess(if (v.ident.prime) Id.memId.toPrime.toVar(state) else Id.memId.toVar(state), Id.getAddr(v.ident, state))
      else v
    case id: IdAccess => id.toVar(state).copy(index = eval(id.index, state, memAccess))
    case BinOp(op, t1, t2, arg1, arg2) =>
      BinOp(op, t1, t2, eval(arg1, state, memAccess), eval(arg2, state, memAccess))
    case PreOp(op, t1, t2, arg) => PreOp(op, t1, t2, eval(arg, state, memAccess))
    case s: VarStore =>
      s.copy(
        array = eval(s.array, state, memAccess),
        index = eval(s.index, state, memAccess),
        exp = eval(s.exp, state, memAccess)
      )
    case a: VarAccess => a.copy(index = eval(a.index, state, memAccess))
    case forall: ForAll =>
      forall.copy(
        bound = forall.bound.map(b => eval(b, state, memAccess)),
        body = eval(forall.body, state, memAccess)
      )
    case _: Lit | _: Const => expr
    case expr =>
      println(s"Unhandled expression(eval): [${expr.getClass()}] $expr")
      expr
  }

  def getBaseVars(vars: Set[Var]): Set[Var] = vars.map(v => v.getBase.resetIndex)
  def getBaseArrays(vars: Set[VarAccess]): Set[VarAccess] = vars.map(v => v.getBase.resetIndex)

  def getRely(exp: Expression, state: State) = {
    val evalExp = eval(exp, state, false)

    eval(
      BinOp.pred(
        "&&",
        constructForall(
          getBaseVars(evalExp.vars - Id.indexId.toVar(state))
            .map(v => {
              if (state.globals.contains(v.ident)) {
                // BinOp(
                //  "&&",
                BinOp.pred(
                  "=>",
                  BinOp("==", Type.TInt, Type.TBool, v, v.toPrime(state)),
                  BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                ) // ,
                //   BinOp("=>", primed(getL(v.ident, state), state), v.toPrime(state).toGamma(state))
                // )
              } else {
                BinOp.pred(
                  "&&",
                  BinOp("==", Type.TInt, Type.TBool, v, v.toPrime(state)),
                  BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                )

              }
            })
            .toList
            ++
              getBaseArrays(evalExp.arrays)
                .map(v => {
                  val pred = if (state.globals.contains(v.ident)) {
                    //  BinOp(
                    //    "&&",
                    BinOp.pred(
                      "=>",
                      BinOp("==", Type.TInt, Type.TBool, v, v.toPrime(state)),
                      BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                    ) //,
                    //    BinOp("=>", primed(getL(v, state), state), v.toPrime(state).toGamma(state))
                    //  )
                  } else {
                    BinOp.pred(
                      "&&",
                      BinOp("==", Type.TInt, Type.TBool, v, v.toPrime(state)),
                      BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                    )
                  }

                  BinOp.pred(
                    "&&",
                    pred,
                    eval(state.arrRelys.getOrElse(v.ident, Const._true), state, false)
                      .subst(Map(Id.indexId.toVar(state) -> Left(eval(v.index, state, false))))
                  )

                })
                .toList
        ),
        eval(state.rely, state, false)
      ),
      state,
      false
    )
  }

  def getL(id: Id, state: State): Expression = {
    if (id == Id.tmpId) Const._true
    else
      eval(
        state.L.getOrElse(id, throw new Error("L not defined for " + id)),
        state,
        false
      )
  }

  def getL(id: IdAccess, state: State): Expression =
    getL(id.ident, state)
      .subst(Map(Id.indexId.toVar(state) -> Left(eval(id.index, state, false))))

  def getL(v: VarAccess, state: State): Expression =
    getL(v.ident, state)
      .subst(Map(Id.indexId.toVar(state) -> Left(eval(v.index, state, false))))

  def primed(p: Expression, state: State) =
    eval(p, state, false).subst(
      (state.ids ++ state.arrayIds)
        .map(id => id.toVar(state) -> Left(id.toPrime.toVar(state)))
        .toMap
    )

  // TODO take havoc statements into account
  def stableR(p: Expression, state: State) =
    eval(
      BinOp.pred("=>", BinOp.pred("&&", getRely(p, state), p), primed(p, state)),
      state,
      true
    )

  def rImplies(p: Expression, state: State) = {
    eval(BinOp.pred("=>", getRely(p, state), primed(p, state)), state, true)
  }

  def stableR(p: Expression, index: Expression, state: State) =
    eval(
      BinOp.pred(
        "=>",
        BinOp.pred(
          "&&",
          getRely(p, state).subst(Map(Id.indexId.toVar(state) -> Left(index))),
          p
        ),
        primed(p, state)
      ),
      state,
      true
    )

  def rImplies(p: Expression, index: Expression, state: State) =
    eval(
      BinOp.pred(
        "=>",
        getRely(p, state).subst(Map(Id.indexId.toVar(state) -> Left(index))),
        primed(p, state)
      ),
      state,
      true
    )

  def guar(a: Assignment, state: State) = {
    val guar = eval(state.guar, state, true)
    val subst = Map(
      (Id.memId.toVar(state) -> Left(Id.memId.toVar(state).toNought)),
      (Id.memId.toPrime.toVar(state) -> Left(Id.memId.toVar(state)))
    )
    val gPrime = guar.subst(subst)
    // val _subst = vars.map(v => v.toNought.asInstanceOf[Var] -> Left(v)).toMap
    val _subst = Map(Id.memId.toVar(state).toNought -> Left(Id.memId.toVar(state)))
    wp(gPrime, a, state).subst(_subst)
  }

  def guar(a: ArrayAssignment, state: State) = {
    val guar =
      eval(
        BinOp.pred(
          "&&",
          state.guar,
          eval(state.arrGuars.getOrElse(a.lhs.ident, Const._true), state, true).subst(Map(Id.indexId.toVar(state) -> Left(a.lhs.index)))
        ),
        state,
        true
      )
    val vars = getBaseVars(guar.vars ++ guar.arrays.map(a => a.name))
    val subst = vars.map(v => List(v -> Left(v.toNought), v.toPrime(state) -> Left(v))).flatten.toMap
    val gPrime = guar.subst(subst)
    val _subst = vars.map(v => v.toNought.asInstanceOf[Var] -> Left(v)).toMap
    wp(gPrime, a, state).subst(_subst)
  }

  def computeGamma(exp: Expression, state: State): Expression = {
    val expEval = eval(exp, state, false)
    constructForall(
      expEval.vars
        .map(v =>
          eval(
            BinOp.pred("||", v.toGamma(state), getL(v.ident, state)),
            state,
            true
          ) // Default to high
        )
        .toList ++
        expEval.arrays
          .map(a => {
            val subst = Map[Var, Left[Expression, Nothing]](Id.indexId.toVar(state) -> Left(eval(a.index, state, false)))
            eval(
              BinOp.pred("||", a.toGamma(state), getL(a.ident, state)).subst(subst),
              state,
              true
            ) // Default to high
          })
          .toList
    )
  }

  def joinStates(states: List[State], state: State, blockName: String) = {
    val indicies = states.foldLeft(state.indicies) { (a, i) =>
      i.indicies.map { case (k, v) => k -> math.max(v, a.getOrElse(k, -1)) }
    }

    val preds = states
      .map(s => {
        s.Qs.map(Q => Q.copy(path = Q.path :+ blockName))
        /*
        if (s.indicies == indicies) s.Qs
        else {
          val conds = s.indicies
            .filter { case (id, int) =>
              indicies.get(id) match {
                case Some(i) => i != int
                case None    => true
              }
            }
            .map { case (id, ind) =>
              BinOp("==", Var(id, ind), Var(id, indicies.getOrElse(id, -1)))
            }
            .toList

          s.Qs.map(info => info.copy(pred = BinOp("=>", constructForall(conds), info.pred)))
        }
         */
      })
      .flatten

    val error = states.foldLeft(state.error) { case (a, i) =>
      if (a || i.error) true else false
    }

    state.copy(
      Qs = preds,
      indicies = indicies,
      error = error
    )
  }
}
