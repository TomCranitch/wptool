package wptool

import scala.util.Try

object Passify {
  def execute(statements: List[Statement], state: PassifyState): (List[Statement], PassifyState) =
    statements match {
    case stmt :: rest =>
      val (st1, state1) = execute(stmt, state)
      val (st2, state2) = execute(rest, state1)
      (st1 :: st2, state2)
    case Nil => (Nil, state)
  }

  def execute(statement: Statement, state: PassifyState): (Statement, PassifyState) = statement match {
    case assign: Assignment =>
      // 1: convert id to var
      // 2: start at index 0 and incrument each time


      //val atomic = Atomic(List(Assert(Unit), Assume(assign.)))
      val rhs = eval(assign.expression, state)
      val (lhs, _state) = idToNewVar(assign.lhs, computeGamma(rhs.variables.toList, state), state)
      val assume = Assume(BinOp("==", lhs, rhs))
      // TODO check default vals
      // TODO need to fix Const._true
      val globalPred = BinOp("=>", Const._true, BinOp("=>", getL(assign.lhs, state), lhs.gamma))
      val controlPred = if (state.state.controls.contains(assign.lhs)) {
        constructForall(state.state.controlledBy.getOrElse(assign.lhs, Set()).map(contr =>
          BinOp(
            "=>",
            getL(contr, state).subst(Map((assign.lhs, rhs))),
            BinOp("||", getGamma(contr, state), getL(contr, state))
          )
        ).toList)
      } else {
        Const._true
      }

      val assert = Assert(BinOp("&&", globalPred, controlPred)) // TODO
      val atomic = Atomic(List(assert, assume))
      (atomic, _state)
    case ifStmt: If =>
      val _test = eval(ifStmt.test, state)
      var (_left: Block, state1: PassifyState) = execute(ifStmt.left, state)
      var (_right: Block, state2: PassifyState) = ifStmt.right match {
        case Some(right: Block) => execute(right, state)
        case None => (Block(List()), state) // Need an empty block to add extra assumes
      }


      // Merge the two maps taking the max of the vals
      val _idToVar: Map[Id, Var] = state1.idVarMap ++ state2.idVarMap.map{case (k, v) => k -> {
        val var1 = state1.idVarMap.get(k)
        var1 match {
          case Some(vari) => {
            val index = math.max(v.index, vari.index)
            // TODO how to compute security
            // Should all instances of a given variable have the same security ?
            // Would need to instanciate new instaces of all vars at the end for the same gamma ?
            val sec = BinOp("&&", v.gamma, vari.gamma)
            Var(k.toString, index, sec, state.L.getOrElse(k, throw new Error("")))
          }
          case None => v
        }
      }}

      for ((k, v) <- _idToVar) {
        // TODO need ot handle var not declared before if
        // TODO is low correct default
        if (state1.idVarMap.getOrElse(k, Var.emptyIndex(-1)).index < v.index) {
          _left = _left.copy(statements = (_left.statements :+ Assume(BinOp("==", k.toVar(v.index, v.gamma, getL(k, state)), state1.idVarMap.getOrElse(k, throw new Error("Variable " + k + "not defined in left branch"))))))
        }

        if (state2.idVarMap.getOrElse(k, Var.emptyIndex(-1)).index < v.index) {
          _right = _right.copy(statements = (_right.statements :+ Assume(BinOp("==", k.toVar(v.index, v.gamma, getL(k, state)), state2.idVarMap.getOrElse(k, throw new Error("Variable " + k + "not defined in right branch"))))))
        }
      }

      val _ifstmt = ifStmt.copy(test = _test, left = _left, right = Some(_right))
      (_ifstmt, state.copy(idVarMap = _idToVar))
    case block: Block =>
      val (stl, idi1) = execute(block.statements, state)
      val block1 = block.copy(statements = stl)
      (block1, idi1)
    case stmt =>
      println("Unimplemented statement: " + stmt)
      (stmt, state)
  }

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

  def computeGamma (variables: List[Var], state: PassifyState): Expression = variables match {
    // TODO check correct
    // Defn of Gamma has been modified - Try(expr.variables.map(id => id.gamma).max).getOrElse(Low)
    case v :: Nil =>
      BinOp("||", getGamma(v.ident, state) , getL(v.ident, state))
    case v :: rest => BinOp("&&", computeGamma(List(v), state), computeGamma(rest, state))
    case Nil => Const._true
  }

  def getGamma (id: Id, state: PassifyState): Expression = {
    eval(Try(state.idVarMap(id).gamma).getOrElse(state.gamma0.getOrElse(id, Low).toTruth), state)
  }

  def idToNewVar(id: Id, gamma: Expression, state: PassifyState): (Var, PassifyState) = {
    val index = state.idVarMap.get(id) match {
      case Some(v) => v.index + 1
      case None => 0
    }
    val vari = id.toVar(index, gamma, getL(id, state))
    val _state = state.copy(idVarMap = state.idVarMap.updated(id, vari))
    (vari, _state)
  }

  def idToVar(id: Id, state: PassifyState): Var = {
    val index = state.idVarMap.getOrElse(id, Var("", 0, Const._true, getL(id, state))).index
    id.toVar(index, getGamma(id, state), getL(id, state))
  }


  def constructForall (exprs: List[Expression]): Expression = exprs match {
    case expr :: Nil => expr
    case expr :: rest =>
      BinOp("&&", expr, constructForall(rest))
    case Nil => Const._true
  }

  def getL (id: Id, state: PassifyState): Expression = {
    eval(state.L.getOrElse(id, throw new Error("L not defined for " + id)), state)
  }
}
