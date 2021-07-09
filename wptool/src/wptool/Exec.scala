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
            // TODO should there be a guaranttee check?
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
      val _state = checkVcs(state.Qs, state.debug, state.simplify, state) match {
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
    case assign @ Assignment(lhs: Identifier, _, _) =>
      val globalPred =
        if (state.globals.contains(lhs.ident))
          BinOp.pred(
            "=>",
            getL(lhs, state),
            computeGamma(assign.expression, state)
          )
        else Const._true
      val controlPred = if (state.controls.contains(lhs)) {
        constructForall(
          state.controlledBy
            .getOrElse(lhs, Set())
            .map(contr => {
              BinOp.pred(
                "=>",
                eval(getL(contr, state).subst((Map(lhs.toVar(state) -> Left(assign.expression)), state)), state, true),
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
            new PredInfo(rImplies(globalPred, state), assign, "L => G"),
            new PredInfo(rImplies(controlPred, state), assign, "secUpd")
          )
          .incPrimeIndicies
      } else {
        _state
          .addQs(
            new PredInfo(globalPred, assign, "L => G"),
            new PredInfo(controlPred, assign, "secUpd")
          )
          .incPrimeIndicies
      }
    case assign @ Assignment(Dereference(id), _, _) =>
      var globalPred: Expression = null
      var controlPred: Expression = null
      id match {
        case id: Id =>
          // Must be global
          globalPred = BinOp.pred(
            "=>",
            getL(id, state),
            computeGamma(assign.expression, state)
          )

          // Check if anything that b points to is a control variable
          controlPred = constructForall(
            state.pointsTo
              .get(id)
              .get
              .filter(i => state.controls.contains(i))
              .map(i => {
                state.controlledBy
                  .getOrElse(i, Set())
                  .map(contr =>
                    BinOp.pred(
                      "=>",
                      eval(getL(contr, state).subst((Map(i.toVar(state) -> Left(assign.expression)), state)), state, true),
                      BinOp.pred("||", eval(contr.toGamma, state, true), getL(contr, state))
                    )
                  )
              })
              .flatten
              .toList
          )
        case _ => throw new Error("Expected id")

      }

      val _state = evalWp(assign, state, RG)

      if (RG) {
        val guarantee = guar(assign, state)

        _state
          .addQs(
            new PredInfo(rImplies(guarantee, state), assign, "Guarantee"),
            new PredInfo(rImplies(globalPred, state), assign, "L => G"),
            new PredInfo(rImplies(controlPred, state), assign, "secUpd")
          )
          .incPrimeIndicies
      } else {
        _state
          .addQs(
            new PredInfo(globalPred, assign, "L => G"),
            new PredInfo(controlPred, assign, "secUpd")
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
                  eval(
                    getL(contr, state).subst((Map(assign.lhs.ident.toVar(state) -> Right((assign.lhs.index, assign.expression))), state)),
                    state,
                    true
                  ),
                  state,
                  true
                ),
                BinOp.pred(
                  "||",
                  eval(contr.toGamma, state, true),
                  eval(getL(contr, state).subst((Map(Id.indexId.toVar(state) -> Left(assign.lhs.index)), state)), state, true)
                )
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
          BinOp.pred("=>", PreOp("!", TBool, TBool, stabRB), eval(exp, state, true))
        )
      case Assert(exp, checkStableR, _) =>
        Q
      case havoc: Havoc => Q
      case assign @ Assignment(lhs: Id, _, _) =>
        val rhsGamma = computeGamma(assign.expression, state)

        eval(
          Q.subst(
            (
              Map(
                (lhs.toGamma.toVar(state) -> Left(rhsGamma)),
                (lhs.toVar(state) -> Left(eval(assign.expression, state, false)))
              ),
              state
            )
          ),
          state,
          false
        )
      case assign @ Assignment(Dereference(id), _, _) =>
        val rhsGamma = computeGamma(assign.expression, state)
        val lhs = eval(assign.lhs, state, false) match {
          case Dereference(v: Var) => v
          case _                   => throw new Error("Unexpected dereference")
        }

        eval(
          Q.subst(
            (
              Map(
                (Dereference(lhs) -> Left(eval(assign.expression, state, true))),
                (Dereference(lhs.toGamma(state)) -> Left(rhsGamma))
              ),
              state
            )
          ),
          state,
          false
        )
      case assign @ Assignment(o @ ObjIdAccess(id, field), _, _) =>
        val rhsGamma = computeGamma(assign.expression, state)
        val lhs = eval(o, state, false) match {
          case lhs: ObjVarAccess => lhs
          case lhs               => throw new Error(s"Unexpected object $lhs (${lhs.getClass})")
        }

        eval(
          Q.subst(
            Map(
              (o.toVar(state) -> Left(eval(assign.expression, state, true))),
              (o.toGamma.toVar(state) -> Left(rhsGamma))
            ),
            state
          ),
          state,
          false
        )
      case assign: ArrayAssignment =>
        val rhsGamma = computeGamma(assign.expression, state)

        eval(
          Q.subst(
            (
              Map(
                (assign.lhs.ident.toGamma.toVar(state) -> Right(
                  (eval(assign.lhs.index, state, true), rhsGamma)
                )),
                (assign.lhs.ident.toVar(state) -> Right(
                  eval(assign.lhs.index, state, true),
                  eval(assign.expression, state, true)
                ))
              ),
              state
            )
          ),
          state,
          false
        )
      case stmt =>
        println(s"Unhandled statement(wp exec): $stmt (${stmt.getClass})")
        Q
    }
  }

  def eval(expr: Expression, state: State, memAccess: Boolean): Expression =
    expr match {
      case id: Id if (id.memLoc)        => id.toVar(state)
      case va: Var if (va.ident.memLoc) => va
      case id: Id if (state.globals.contains(id.getBase)) =>
        val mem =
          (if (id.prime) Id.memId.toPrime.toVar(state) else if (id.nought) Id.memId.toVar(state).toNought else Id.memId.toVar(state))
        if (id == Id.indexId) id.toVar(state)
        else if (id.memLoc) id.toVar(state)
        else if (memAccess && !id.gamma)
          VarAccess(mem, eval(Id.getAddr(id, state), state, true))
        else if (memAccess && id.gamma)
          VarAccess(mem.toGamma(state), eval(Id.getAddr(id, state), state, true))
        else
          id.toVar(state)
      case id: Id => id.toVar(state)
      case v: Var if (state.globals.contains(v.ident.getBase)) =>
        val mem =
          (if (v.ident.prime) Id.memId.toPrime.toVar(state)
           else if (v.ident.nought) Id.memId.toVar(state).toNought
           else Id.memId.toVar(state))
        if (v.ident == Id.indexId) v
        else if (memAccess && !v.ident.gamma)
          VarAccess(mem, eval(Id.getAddr(v.ident, state), state, true))
        else if (memAccess && v.ident.gamma)
          VarAccess(mem.toGamma(state), eval(Id.getAddr(v.ident, state), state, true))
        else v
      case id: IdAccess => id.toVar(state).copy(index = eval(id.index, state, memAccess))
      case idObj: ObjIdAccess =>
        val mem =
          (if (idObj.ident.prime) Id.memId.toPrime.toVar(state)
           else if (idObj.ident.nought) Id.memId.toVar(state).toNought
           else Id.memId.toVar(state))
        if (memAccess) VarAccess(mem, eval(idObj.getAddr(state), state, true))
        else idObj.toVar(state)
      case varObj: ObjVarAccess =>
        val mem =
          (if (varObj.ident.prime) Id.memId.toPrime.toVar(state)
           else if (varObj.ident.nought) Id.memId.toVar(state).toNought
           else Id.memId.toVar(state))
        if (memAccess) VarAccess(mem, eval(varObj.getAddr(state), state, true))
        else varObj
      case deref @ Dereference(id) =>
        deref.copy(ident = eval(deref.ident, state, false)) match {
          case Dereference(v: Var) if (memAccess) =>
            val memId = v.copy(ident = v.ident.copy(name = Id.memId.name))
            VarAccess(memId, eval(VarAccess(memId, state.addrs.get(v.ident).get), state, true))
          case d @ _ => d
        }
      case r @ Reference(id) =>
        r.copy(ident = eval(r.ident, state, false)) match {
          case Reference(v: Var) => eval(state.addrs.get(v.ident).get, state, true)
          case r @ _             => r
        }
      case BinOp(op, t1, t2, arg1, arg2) =>
        BinOp(op, t1, t2, eval(arg1, state, memAccess), eval(arg2, state, memAccess))
      case PreOp(op, t1, t2, arg) => PreOp(op, t1, t2, eval(arg, state, memAccess))
      case Declassify(e, d)       => eval(e, state, memAccess)
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
      case _: Lit | _: Const | _: Var => expr
      case expr =>
        println(s"Unhandled expression(eval): [${expr.getClass()}] $expr")
        expr
    }

  private def skipMemLocs(v: Variable) = v match {
    case v: Var if (v.ident.memLoc) => false
    case v                          => true
  }

  def getBaseVars(vars: Set[Variable]): Set[Variable] = vars
    .filter(skipMemLocs)
    .map(v =>
      v.getBase.resetIndex match {
        case v: VarAccess => v.name
        case v @ _        => v
      }
    )
  def getBaseVariables(vars: Set[Variable]): Set[Variable] = vars.filter(skipMemLocs).map(v => v.getBase.resetIndex)

  def getRely(exp: Expression, state: State) = {
    val evalExp = eval(exp, state, false)

    val p =
      constructForall(
        getBaseVariables(evalExp.vars - Id.indexId.toVar(state))
          .map(v => {
            val pred = if (state.globals.contains(v.ident) || v.ident.getBase == Id.memId) {
              // BinOp(
              //  "&&",
              BinOp.pred(
                "=>",
                BinOp("==", TInt, TBool, v, v.toPrime(state)),
                BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
              ) // ,
              //   BinOp("=>", primed(getL(v.ident, state), state), v.toPrime(state).toGamma(state))
              // )
            } else {
              BinOp.pred(
                "&&",
                BinOp("==", TInt, TBool, v, v.toPrime(state)),
                BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
              )

            }

            v match {
              case m: VarAccess if (m.ident == Id.memId) => pred
              case v: VarAccess =>
                BinOp.pred(
                  "&&",
                  pred,
                  eval(
                    eval(state.arrRelys.getOrElse(v.ident, Const._true), state, false)
                      .subst((Map(Id.indexId.toVar(state) -> Left(eval(v.index, state, false))), state)),
                    state,
                    false
                  )
                )

              case _ => pred
            }
          })
          .toList
      )

    eval(
      BinOp.pred(
        "&&",
        constructForall(
          getBaseVariables(evalExp.vars - Id.indexId.toVar(state))
            .map(v => {
              val pred = if (state.globals.contains(v.ident) || v.ident.getBase == Id.memId) {
                // BinOp(
                //  "&&",
                BinOp.pred(
                  "=>",
                  BinOp("==", TInt, TBool, v, v.toPrime(state)),
                  BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                ) // ,
                //   BinOp("=>", primed(getL(v.ident, state), state), v.toPrime(state).toGamma(state))
                // )
              } else {
                BinOp.pred(
                  "&&",
                  BinOp("==", TInt, TBool, v, v.toPrime(state)),
                  BinOp.pred("==", v.toGamma(state), v.toPrime(state).toGamma(state))
                )

              }

              v match {
                case m: VarAccess if (m.ident == Id.memId) => pred
                case v: VarAccess =>
                  BinOp.pred(
                    "&&",
                    pred,
                    eval(state.arrRelys.getOrElse(v.ident, Const._true), state, false)
                      .subst((Map(Id.indexId.toVar(state) -> Left(eval(v.index, state, false))), state))
                  )

                case _ => pred
              }
            })
            .toList
        ),
        eval(state.rely, state, false)
      ),
      state,
      true
    )
  }

  def getL(id: Identifier, state: State): Expression = id match {
    case Id.tmpId              => Const._true
    case id: Id if (id.memLoc) => Const._true
    case _: IdAccess | _: VarAccess =>
      id match {
        case id: IdAccess =>
          eval(
            getL(id.ident, state).subst(
              (Map(Id.indexId.toVar(state) -> Left(eval(id.index, state, true))), state)
            ),
            state,
            true
          )
        case id: VarAccess =>
          eval(
            getL(id.ident, state).subst(
              (Map(Id.indexId.toVar(state) -> Left(eval(id.index, state, true))), state)
            ),
            state,
            true
          )
      }
    case id: Identifier =>
      eval(
        state.L.getOrElse(id, throw new Error("L not defined for " + id)),
        state,
        true
      )
  }

  def primed(p: Expression, state: State) =
    eval(
      eval(p, state, false).subst(
        (
          (state.arrayIds + Id.memId)
            .map(id => id.toVar(state) -> Left(id.toPrime.toVar(state)))
            .toMap,
          state
        )
      ),
      state,
      false
    )

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
          getRely(p, state).subst((Map(Id.indexId.toVar(state) -> Left(index)), state)),
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
        getRely(p, state).subst((Map(Id.indexId.toVar(state) -> Left(index)), state)),
        primed(p, state)
      ),
      state,
      true
    )

  def guar(a: Assignment, state: State) = {
    val guar = eval(state.guar, state, false)
    val vars = getBaseVars(guar.vars)
    val subst = vars.map(v => List(v -> Left(v.toNought), v.toPrime(state) -> Left(v))).flatten.toMap[Expression, Left[Expression, Nothing]]
    val gPrime = guar.subst((subst, state))
    val _subst = Map[Expression, Left[Expression, Nothing]](Id.memId.toVar(state).toNought -> Left(Id.memId.toVar(state)))
    eval(wp(eval(gPrime, state, true), a, state).subst((_subst, state)), state, true)
  }

  def guar(a: ArrayAssignment, state: State) = {
    val guar =
      eval(
        BinOp.pred(
          "&&",
          state.guar,
          eval(state.arrGuars.getOrElse(a.lhs.ident, Const._true), state, true)
            .subst((Map(Id.indexId.toVar(state) -> Left(a.lhs.index)), state))
        ),
        state,
        true
      )
    val vars = getBaseVars(guar.vars)
    val subst = vars.map(v => List(v -> Left(v.toNought), v.toPrime(state) -> Left(v))).flatten.toMap[Expression, Left[Expression, Nothing]]
    val gPrime = eval(guar.subst((subst, state)), state, true)
    val _subst = vars.map(v => v.toNought.asInstanceOf[Var] -> Left(v)).toMap[Expression, Left[Expression, Nothing]]
    eval(wp(gPrime, a, state).subst((_subst, state)), state, true)
  }

  def computeGamma(exp: Expression, state: State): Expression = {
    val expEval = eval(exp, state, false)
    val basePred = constructForall(
      expEval.vars
        .map(v => {
          eval(
            BinOp.pred("||", v.toGamma(state), getL(v.ident, state)),
            // BinOp.pred("||", VarAccess(Id.memId.toGamma.toVar(state), Id.getAddr(v.ident, state)), getL(v.ident, state)),
            state,
            true
          ) // Default to high

        })
        .toList
    )

    exp match {
      case Declassify(_, d)                           => BinOp.pred("||", d, basePred)
      case PreOp("!", TBool, TBool, Declassify(_, d)) => BinOp.pred("||", d, basePred) // TODO there should be a better way to do this
      case _                                          => basePred
    }
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
