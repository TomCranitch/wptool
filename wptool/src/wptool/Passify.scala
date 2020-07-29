package wptool

import scala.util.Try

object Passify {
  def execute(statements: List[Statement], state: PassifyState): (List[Statement], PassifyState) =
    statements match {
    case stmt :: rest =>
      val (st, idi) = execute(stmt, state)
      val (stl, idi1) = execute(rest, state)
      (st :: stl, idi1)
    case Nil => (Nil, state)
  }

  def execute(statement: Statement, state: PassifyState): (Statement, PassifyState) = statement match {
    case assign: Assignment =>
      // 1: convert id to var
      // 2: start at index 0 and incrument each time


      //val atomic = Atomic(List(Assert(Unit), Assume(assign.)))
      // TODO: assert
      val _state = updateVarIndex(assign.lhs, state)
      val lhs = idToVar(assign.lhs, state)
      val rhs = eval(assign.expression, state)
      val _lhs = lhs.copy(gamma = computeGamma(rhs, _state))
      val assume = Assume(BinOp("==", lhs, rhs))
      // TODO check default vals
      val globalPred = BinOp("=>", Const._true, BinOp("=>", eval(state.state.L.getOrElse(assign.lhs, Const._false), _state), _lhs.gamma.toTruth))// Gamma(assign.expression.variables)))
      val controlPred = if (state.state.controls.contains(assign.lhs)) {
        constructForall(state.state.controlledBy.getOrElse(assign.lhs, Set()).map(contr =>
          // TODO default val
          BinOp(
            "=>",
            BinOp("=>", BinOp("==", _lhs, rhs), eval(state.state.L.getOrElse(contr, throw new Error("No L(x) defined")), state)),
            BinOp("||", getGamma(contr, state).toTruth, eval(state.state.L.getOrElse(contr, throw new Error("No L(x) defined")), state))
          )
        ).toList)

        // TODO
        //Const._true
      } else {
        Const._true
      }

      println("SMT: " + SMT.proveExpression(BinOp("&&", globalPred, controlPred), debug=false))
      SMT.simplify(BinOp("&&", globalPred, controlPred))

      // val controlPred = if (SMT.proveExpression(_controlPred, debug = false)) Const._true else Const._false

      println(controlPred)
      println(SMT.proveExpression(controlPred, false))
      val assert = Assert(BinOp("&&", globalPred, controlPred)) // TODO
      val atomic = Atomic(List(assert, assume))
      (atomic, _state)
    case ifStmt: If =>
      // 1: evaluate each branch separately (and maintain a list of modified vars)
      // 2: for each var introduce a new var with an index one higher then the max

      // If no else compare based on existing idindices

      val _test = eval(ifStmt.test, state)
      var (_left: Block, state1: PassifyState) = execute(ifStmt.left, state)
      var (_right: Block, state2: PassifyState) = ifStmt.right match {
        case Some(right: Block) => execute(right, state)
        case None => (Block(List()), state) // Need an empty block to add extra assumes
      }


      // Merge the two maps taking the max of the vals
      val _idToVar: Map[Id, Var] = state1.idVarMap ++ state2.idVarMap.map{case (k, v) => k -> {
        val var1 = state1.idVarMap.getOrElse(k, Var("", 0, High))
        val index = math.max(v.index, var1.index)
        val sec = Set(v.gamma, var1.gamma).max
        Var (k.toString, index, sec)
      }}

      for ((k, v) <- _idToVar) {
        // TODO need ot handle var not declared before if

        // TODO is low correct default
        _left = _left.copy(statements = (_left.statements :+ Assume(BinOp("==", k.toVar(v.index + 1, v.gamma), state1.idVarMap.getOrElse(k, throw new Error("Variable " + k + "not defined in left branch"))))))
        _right = _right.copy(statements = (_right.statements :+ Assume(BinOp("==", k.toVar(v.index + 1, v.gamma), state2.idVarMap.getOrElse(k, throw new Error("Variable " + k + "not defined in right branch"))))))
      }

      val _ifstmt = ifStmt.copy(test = _test, left = _left, right = Some(_right))
      // TODO: when merging from if do we need to add additional proof obligations

      // TODO: anything else from state need to be merged ??
      (_ifstmt, state.copy(idVarMap = _idToVar))
    case block: Block =>
      val (stl, idi1) = execute(block.statements, state)
      val block1 = block.copy(statements = stl)
      (block1, idi1)
    case stmt =>
      println("Unimplemented statement: " + stmt)
      (stmt, state)
  }

  def idToVar(id: Id, state: PassifyState): Var = {
    state.idVarMap.getOrElse(id, id.toVar(0, state.Gamma.getOrElse(id, Low)))
  }

  // TODO eval for expression
  def eval(expr: Expression, state: PassifyState): Expression = expr match {
    case id: Id => idToVar(id, state)
    case id: Var => id
      // Id(id.name, state.idIndices.getOrElse(id.name, 0))
    case BinOp(op, arg1, arg2) =>
      val _arg1 = eval(arg1, state)
      val _arg2 = eval(arg2, state)
      BinOp(op, _arg1, _arg2)
    case _: Lit | _: Const => expr
    case expr =>
      println("Unimplemented expression: " + expr + " " + expr.getClass)
      expr
  }

  def updateVarIndex (id: Id, state: PassifyState): PassifyState = {
    val vari = state.idVarMap.getOrElse(id, id.toVar(-1, state.Gamma.getOrElse(id, Low)))
    state.copy(idVarMap = state.idVarMap.updated(id, vari.copy(index = vari.index + 1)))
  }

  def computeGamma (expr: Expression, state: PassifyState): Security = {
    Try(expr.variables.map(id => id.gamma).max).getOrElse(Low)
  }

  def getGamma (id: Id, state: PassifyState): Security = {
    Try(state.idVarMap(id).gamma).getOrElse(state.Gamma.getOrElse(id, Low))
  }

  def constructForall (exprs: List[Expression]): Expression = exprs match {
    case expr :: Nil => expr
    case expr :: rest =>
      BinOp("&&", expr, constructForall(rest))
    case Nil => Const._true // TODO
  }
}
