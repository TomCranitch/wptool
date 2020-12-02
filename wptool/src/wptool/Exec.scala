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
    case atomic: Atomic =>
      // TODO check
      exec(atomic.statements, state)
    case block: Block =>
      exec(block.statements, state)
    case Assignment(lhs, cas: CompareAndSwap) =>
      val gamma = computeGamma(cas.e1.ids.toList :+ cas.x, state)
      val _left = BinOp("&&", guar(Assignment(cas.x, cas.e2), state), exec(Assignment(cas.x, cas.e2), exec(Assignment(lhs, Lit(0)), state), RG = false).Q)
      val left = BinOp("=>", BinOp("==", cas.x, cas.e1), _left) 
      val right = BinOp("=>", BinOp("!=", cas.x, cas.e1), exec(Assignment(lhs, Lit(1)), state).Q) 
      val pred = constructForall(List(gamma, left, right))
      state.copy(Q = rImplies(pred, state)).incIndicies
    case If(cas: CompareAndSwap, c1, c2) =>
      val state1 = exec(Assignment(cas.x, cas.e2), exec(c1, state), RG = false)
      val state2 = exec(c2.get, state) // Right should contain block from passification
      val left = BinOp("=>", BinOp("==", cas.x, cas.e1), BinOp("&&", guar(Assignment(cas.x, cas.e2), state), state1.Q))
      val right = BinOp("=>", BinOp("!=", cas.x, cas.e2), state2.Q)
      val condGamma = computeGamma(cas.e1.ids.toList :+ cas.x, state)
      val pred = constructForall(List(left, right, condGamma))
      state.copy(Q = rImplies(pred, state)).incIndicies
    case While(cas: CompareAndSwap, inv, gamma, _, c) =>
      val body = exec(Assignment(cas.x, cas.e2), exec(c, state.copy(Q = inv)), RG = false)
      val test = BinOp("=>", inv, computeGamma(cas.e1.ids.toList :+ cas.x, state))
      val left = BinOp("=>", BinOp("&&", inv, BinOp("==", cas.x, cas.e1)), guar(Assignment(cas.x, cas.e2), body))
      val right = BinOp("=>", BinOp("&&", inv, BinOp("!=", inv, cas.x)), state.Q)
      state.copy(Q = constructForall(List(inv, stableR(inv, state), left, right))).incIndicies
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


      if (RG) {
        val guarantee = guar(assign, state)
        val pred = constructForall(List(PO, Q, guarantee))

        //state.copy(Q = BinOp("&&", guarantee, rImplies(pred, state))).incIndicies
        state.copy(Q = rImplies(pred, state)).incIndicies
      } else {
        state.copy(Q = BinOp("&&", PO, Q)).incIndicies
      }


    case ifStmt: If =>
      val state1 = exec(ifStmt.left, state)
      val state2 = exec(ifStmt.right.get, state) // Right should contain block from passification
      val left = BinOp("=>", ifStmt.test, state1.Q)
      val right = BinOp("=>", PreOp("!", ifStmt.test), state2.Q)
      val stableRImp = BinOp("=>", stableR(ifStmt.test, state), BinOp("&&", left, right))
      val condGamma = computeGamma(ifStmt.test.ids.toList, state)
      // TODO is this pred correct
      val notStableRImo = BinOp("=>", PreOp("!", stableR(ifStmt.test, state)), BinOp("&&", state1.Q, state2.Q))

      // TODO include Q??
      state.copy(Q = constructForall(List(rImplies(condGamma, state), stableRImp, notStableRImo))).incIndicies

    case loop: While => 
      val gammaPred = constructForall(loop.gamma.map(x => BinOp("==", GammaId(x.variable), x.security.toTruth)))
      val inv = BinOp("&&", gammaPred, loop.invariant)
      val condGamma = computeGamma(loop.test.ids.toList, state)
      val PO = BinOp("&&", eval(inv, state), BinOp("=>", eval(inv, state), condGamma))
      // TODO i dont think this considers forall sigma
      val body = exec(loop.body, state.copy(Q=eval(inv, state)))
      val wpQ = BinOp("&&", BinOp("=>", BinOp("&&", eval(inv, state), eval(loop.test, state)), body.Q), BinOp("=>", BinOp("&&", eval(inv, state), PreOp("!", eval(loop.test, state))), state.Q))
      // TODO check use of stableR
      state.copy(Q = constructForall(List(PO, stableR(inv, state), wpQ))).incIndicies

    case stmt =>
      println("Unhandled statement: " + stmt)
      state.incIndicies
  }

  def eval (expr: Expression, state: State): Expression = expr match {
    case BinOp(op, arg1, arg2) => BinOp(op, eval(arg1, state), eval(arg2, state))
    case _: Lit | _: Const | _: Id | _: GammaId  => expr
    case _: CompareAndSwap => throw new Error("Unexpected compare and swap")
    case expr =>
      println("Unhandled expression: " + expr)
      expr
  }

  def evalPrimed (expr: Expression, state: State): Expression = {
  expr match {
    case BinOp(op, arg1, arg2) => BinOp(op, evalPrimed(arg1, state), evalPrimed(arg2, state))
    case PreOp(op, arg) => PreOp(op, evalPrimed(arg, state))
    case _: Lit | _: Const  => expr
    case id: Id => 
      if (id.name.endsWith("'")) id.indexPrime(state)
      else id
    case id: GammaId => 
      if (id.ident.name.endsWith("'")) id.indexPrime(state)
      else id
    case _: CompareAndSwap => throw new Error("Unexpected compare and swap")
    case expr =>
      println("Unhandled expression (eval primed): " + expr)
      expr
  }
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

  def primed (p: Expression, state: State) = p.subst(state.ids.map(id => id -> id.prime).toMap)

  // TODO maybe only use relevant parts of the axioms
  def stableR (p: Expression, state: State) = evalPrimed(BinOp("=>", BinOp("&&", state.rely, p), primed(p, state)), state)

  def rImplies (p: Expression, state: State) = evalPrimed(BinOp("=>", state.rely, primed(p, state)), state)

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
