// TODO this leads to problems because you need to step forward to get the Gamma, but that then requires the PO are generated here

package wptool

import scala.util.Try

object Preprocess {
  def execute(statements: List[Statement], state: PassifyState): (List[Statement], PassifyState) =
    statements match {
    case stmt :: rest =>
      val (st1, state1) = execute(stmt, state)
      val (st2, state2) = execute(rest, state1)
      (st1 :: st2, state2)
    case Nil => (Nil, state)
  }

  def execute(statement: Statement, state: PassifyState): (Statement, PassifyState) = statement match {
    case Assignment(lhs, rhs) =>
      val _rhs = eval(rhs, state)
      val (vari, _state) = idToNewVar(lhs, computeGamma(_rhs.variables.toList, state), state)
      (VarAssignment(vari, _rhs), _state)
    case ifStmt: If =>
      // TODO
      val _test = eval(ifStmt.test, state)
      var (_left: Block, state1: PassifyState) = execute(ifStmt.left, state)
      var (_right: Block, state2: PassifyState) = ifStmt.right match {
        case Some(right: Block) => execute(right, state)
        case None => (None, state)
      }


      // Merge the two maps taking the max of the vals
      val _idToVar: Map[Id, Var] = state1.idVarMap ++ state2.idVarMap.map{case (k, v) => k -> {
        val var1 = state1.idVarMap.get(k)
        var1 match {
          case Some(vari) => {
            // TODO how to compute security

            // TODO should this be b => v.gamma && ~b => vari.gamma??
            val sec = BinOp("&&", v.gamma, vari.gamma)
            Var(k.toString, 0, sec, state.L.getOrElse(k, throw new Error("")))
          }
          case None => v
        }
      }}

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
    val vari = id.toVar(0, gamma, getL(id, state))
    val _state = state.copy(idVarMap = state.idVarMap.updated(id, vari))
    (vari, _state)
  }

  def idToVar(id: Id, state: PassifyState): Var = {
    id.toVar(0, getGamma(id, state), getL(id, state))
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
