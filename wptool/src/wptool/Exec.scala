package wptool

object Exec {
  @scala.annotation.tailrec
  def exec(
      statements: List[Statement],
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

  def exec(stmt: Statement, state: State, RG: Boolean): State = stmt match {
    case block: Block =>
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
          state
        ),
        RG
      )
      _state
    case assume: Assume => evalWp(assume, state, RG).incPrimeIndicies
    case assert: Assert =>
      val _state = evalWp(assert, state, RG)
      if (assert.checkStableR)
        _state
          .addQs(
            PredInfo(
              stableR(assert.expression, state),
              assert,
              "StableR"
            )
          )
          .incPrimeIndicies
      else
        _state
          .addQs(
            PredInfo(
              eval(assert.expression, state),
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

      _state.copy(Qs = List(PredInfo(Const._true, EmptyStmt, "initial havoc")))
    case guard: Guard =>
      val _state = evalWp(guard, state, RG)
      if (RG) {
        val gamma = computeGamma(guard.test, state)
        val stabR = stableR(gamma, state)
        _state
          .addQs(
            PredInfo(gamma, guard, "Gamma"),
            PredInfo(stabR, guard, "StableR")
          )
          .incPrimeIndicies
      } else {
        _state.incPrimeIndicies
      }
    case assign: Assignment =>
      val globalPred =
        if (state.globals.contains(assign.lhs))
          BinOp(
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
              BinOp(
                "=>",
                eval(getL(contr, state).subst(Map(assign.lhs.toVar(state) -> Left(assign.expression))), state), // TODO
                BinOp("||", eval(contr.toGamma, state), getL(contr, state))
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
            PredInfo(rImplies(guarantee, state), assign, "Guarantee"),
            PredInfo(rImplies(globalPred, state), assign, "Global"),
            PredInfo(rImplies(controlPred, state), assign, "Control")
          )
          .incPrimeIndicies
      } else {
        _state
          .addQs(
            PredInfo(globalPred, assign, "Global"),
            PredInfo(controlPred, assign, "Control")
          )
          .incPrimeIndicies
      }
    case assign: ArrayAssignment =>
      val indexSub =
        Map(Id.indexId.toVar(state) -> assign.lhs.ident)
      val globalPred =
        if (state.globals.contains(assign.lhs.ident))
          BinOp(
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
              BinOp(
                "=>",
                eval(
                  getL(contr, state).subst(Map(assign.lhs.ident.toVar(state) -> Right((assign.lhs.index, assign.expression)))),
                  state
                ), // TODO
                BinOp(
                  "||",
                  eval(contr.toGamma, state),
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
            PredInfo(
              rImplies(guarantee, assign.lhs.index, state),
              assign,
              "Guarantee"
            ),
            PredInfo(
              rImplies(globalPred, assign.lhs.index, state),
              assign,
              "Global"
            ),
            PredInfo(
              rImplies(controlPred, assign.lhs.index, state),
              assign,
              "Control"
            ),
            PredInfo(
              rImplies(gammaPred, assign.lhs.index, state),
              assign,
              "Index Gamma"
            )
          )
          .incPrimeIndicies
      } else {
        _state
          .addQs(
            PredInfo(
              globalPred,
              assign,
              "Global"
            ),
            PredInfo(
              controlPred,
              assign,
              "Control"
            ),
            PredInfo(
              gammaPred,
              assign,
              "Index Gamma"
            )
          )
          .incPrimeIndicies
      }
    case stmt =>
      println(s"Unhandled statement(wpif exec): $stmt")
      state.incPrimeIndicies
  }

  def evalWp(stmt: Statement, state: State, RG: Boolean) = {
    // if (RG) state.copy(Qs = state.Qs.map(Q => Q.copy(pred = BinOp("&&", wp(Q.pred, stmt, state), stableR(wp(Q.pred, stmt, state), state)))))
    // TODO should use rImplies
    // is this even possible? if the rely is false then the whole expression becomes true
    if (RG) state.copy(Qs = state.Qs.map(Q => Q.copy(pred = rImplies(wp(Q.pred, stmt, state), state))))
    else state.copy(Qs = state.Qs.map(Q => Q.copy(pred = wp(Q.pred, stmt, state))))
    // state.copy(Qs = state.Qs.map(Q => Q.copy(pred = wp(Q.pred, stmt, state))))
  }

  def wp(Q: Expression, stmt: Statement, state: State): Expression = {
    stmt match {
      case Assume(exp) => BinOp("=>", eval(exp, state), Q)
      case Guard(exp) =>
        val stabRB = stableR(exp, state)
        BinOp(
          "&&",
          BinOp("=>", BinOp("&&", eval(exp, state), stabRB), Q),
          BinOp("=>", PreOp("!", stabRB), eval(exp, state))
        )
      case Assert(exp, checkStableR) =>
        /* BinOp(
          "&&",
          eval(exp, state),
          Q
        ) // Potentially move to exec to evaluate separately
         */
        Q
      case havoc: Havoc => Q
      case assign: Assignment =>
        val rhsGamma = computeGamma(assign.expression, state)

        Q.subst(
          Map(
            (assign.lhs.toGamma.toVar(state) -> Left(rhsGamma)),
            (assign.lhs.toVar(state) -> Left(eval(assign.expression, state)))
          )
        )
      case assign: ArrayAssignment =>
        val rhsGamma = computeGamma(assign.expression, state)

        Q.subst(
          Map(
            (assign.lhs.ident.toGamma.toVar(state) -> Right(
              (eval(assign.lhs.index, state), rhsGamma)
            )),
            (assign.lhs.ident.toVar(state) -> Right(
              eval(assign.lhs.index, state),
              eval(assign.expression, state)
            ))
          )
        )
      case stmt =>
        println("Unhandled statement(wp exec): " + stmt)
        Q
    }
  }

  def eval(expr: Expression, state: State): Expression = expr match {
    case id: Id       => id.toVar(state)
    case id: IdAccess => id.toVar(state).copy(index = eval(id.index, state))
    case BinOp(op, arg1, arg2) =>
      BinOp(op, eval(arg1, state), eval(arg2, state))
    case PreOp(op, arg) => PreOp(op, eval(arg, state))
    case s: VarStore =>
      s.copy(
        array = eval(s.array, state),
        index = eval(s.index, state),
        exp = eval(s.exp, state)
      )
    case a: VarAccess => a.copy(index = eval(a.index, state))
    case forall: ForAll =>
      forall.copy(
        bound = forall.bound.map(b => eval(b, state)),
        body = eval(forall.body, state)
      )
    case _: Lit | _: Const | _: Var => expr
    case expr =>
      println(s"Unhandled expression(eval): [${expr.getClass()}] $expr")
      expr
  }

  def getBaseVars(vars: Set[Var]) = vars.map { case Var(Id(name, _, _, _), _, t) => Var(Id(name, false, false, false), 0, t) }

  def getBaseArrays(vars: Set[VarAccess]) = vars.map { case VarAccess(Var(Id(name, _, _, _), _, t), index) =>
    VarAccess(Var(Id(name, false, false, false), 0, t), index)
  }

  def getRely(exp: Expression, state: State) = {
    // TODO i think arrays will need different rules
    val evalExp = eval(exp, state)

    eval(
      BinOp(
        "&&",
        constructForall(
          getBaseVars(evalExp.vars - Id.indexId.toVar(state))
            .map(v => {
              if (state.globals.contains(v.ident)) {
                // BinOp(
                //  "&&",
                BinOp(
                  "=>",
                  BinOp("==", v, v.toPrime(state)),
                  BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                ) // ,
                //   BinOp("=>", primed(getL(v.ident, state), state), v.toPrime(state).toGamma(state))
                // )
              } else {
                BinOp(
                  "&&",
                  BinOp("==", v, v.toPrime(state)),
                  BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state))
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
                    BinOp(
                      "=>",
                      BinOp("==", v, v.toPrime(state)),
                      BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                    ) //,
                    //    BinOp("=>", primed(getL(v, state), state), v.toPrime(state).toGamma(state))
                    //  )
                  } else {
                    BinOp(
                      "&&",
                      BinOp("==", v, v.toPrime(state)),
                      BinOp("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                    )
                  }

                  BinOp(
                    "&&",
                    pred,
                    eval(state.arrRelys.getOrElse(v.ident, Const._true), state)
                      .subst(Map(Id.indexId.toVar(state) -> Left(eval(v.index, state))))
                  )

                })
                .toList
        ),
        eval(state.rely, state)
      ),
      state
    )
  }

  def getL(id: Id, state: State): Expression = {
    if (id == Id.tmpId) Const._true
    else
      eval(
        state.L.getOrElse(id, throw new Error("L not defined for " + id)),
        state
      )
  }

  def getL(id: IdAccess, state: State): Expression =
    getL(id.ident, state)
      .subst(Map(Id.indexId.toVar(state) -> Left(eval(id.index, state))))

  def getL(v: VarAccess, state: State): Expression =
    getL(v.ident, state)
      .subst(Map(Id.indexId.toVar(state) -> Left(eval(v.index, state))))

  def primed(p: Expression, state: State) =
    eval(p, state).subst(
      (state.ids ++ state.arrayIds)
        .map(id => id.toVar(state) -> Left(id.toPrime.toVar(state)))
        .toMap
    )

  // TODO take havoc statements into account
  def stableR(p: Expression, state: State) =
    eval(
      BinOp("=>", BinOp("&&", getRely(p, state), p), primed(p, state)),
      state
    )

  def rImplies(p: Expression, state: State) = {
    eval(BinOp("=>", getRely(p, state), primed(p, state)), state)
  }

  def stableR(p: Expression, index: Expression, state: State) =
    eval(
      BinOp(
        "=>",
        BinOp(
          "&&",
          getRely(p, state).subst(Map(Id.indexId.toVar(state) -> Left(index))),
          p
        ),
        primed(p, state)
      ),
      state
    )

  def rImplies(p: Expression, index: Expression, state: State) =
    eval(
      BinOp(
        "=>",
        getRely(p, state).subst(Map(Id.indexId.toVar(state) -> Left(index))),
        primed(p, state)
      ),
      state
    )

  def guar(a: Assignment, state: State) = {
    val guar = eval(state.guar, state)
    val vars = getBaseVars(guar.vars ++ guar.arrays.map(a => a.name))
    val subst = vars.map(v => List(v -> Left(v.toNought), v.toPrime(state) -> Left(v))).flatten.toMap
    val gPrime = guar.subst(subst)
    val _subst = vars.map(v => v.toNought -> Left(v)).toMap
    wp(gPrime, a, state).subst(_subst)
  }

  // TODO fix subst when multiple arrays present (does this really matter tho or is it handled automatically)
  def guar(a: ArrayAssignment, state: State) = {
    val guar =
      eval(
        BinOp(
          "&&",
          state.guar,
          eval(state.arrGuars.getOrElse(a.lhs.ident, Const._true), state).subst(Map(Id.indexId.toVar(state) -> Left(a.lhs.index)))
        ),
        state
      )
    val vars = getBaseVars(guar.vars ++ guar.arrays.map(a => a.name))
    val subst = vars.map(v => List(v -> Left(v.toNought), v.toPrime(state) -> Left(v))).flatten.toMap
    val gPrime = guar.subst(subst)
    val _subst = vars.map(v => v.toNought -> Left(v)).toMap
    wp(gPrime, a, state).subst(_subst)
  }

  def computeGamma(exp: Expression, state: State): Expression = {
    val expEval = eval(exp, state)
    constructForall(
      expEval.vars
        .map(v =>
          eval(
            BinOp("||", v.toGamma(state), getL(v.ident, state)),
            state
          ) // Default to high
        )
        .toList ++
        expEval.arrays
          .map(a => {
            val subst = Map(Id.indexId.toVar(state) -> Left(eval(a.index, state)))
            eval(
              BinOp("||", a.toGamma(state), getL(a.ident, state)).subst(subst),
              state
            ) // Default to high
          })
          .toList
    )
  }

  def joinStates(states: List[State], state: State) = {
    val indicies = states.foldLeft(state.indicies) { (a, i) =>
      i.indicies.map { case (k, v) => k -> math.max(v, a.getOrElse(k, -1)) }
    }

    val preds = states
      .map(s => {
        s.Qs
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
