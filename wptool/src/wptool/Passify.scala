package wptool

object Passify {
  def execute(statements: List[Statement], idIndices: Map[String, Int], state: State): (List[Statement], Map[String, Int]) =
    statements match {
    case stmt :: rest =>
      val (st, idi) = execute(stmt, idIndices, state)
      val (stl, idi1) = execute(rest, idi, state)
      (st :: stl, idi1)
    case Nil => (Nil, idIndices)
  }

  def execute(statement: Statement, idIndices: Map[String, Int], state: State): (Statement, Map[String, Int]) = statement match {
    case assign: Assignment =>
      // 1: convert id to var
      // 2: start at index 0 and incrument each time


      //val atomic = Atomic(List(Assert(Unit), Assume(assign.)))
      // TODO: assert
      val idIndices1 = updateVarIndex(assign.lhs, idIndices)
      val lhs = assign.lhs.copy(index = idIndices1.getOrElse(assign.lhs.name, 0))
      val assume = Assume(BinOp("==", lhs, assign.expression))
      // TODO gamma not known at 'compile' time
      println(state.L.getOrElse(assign.lhs, Const._false))
      println(eval(state.L.getOrElse(assign.lhs, Const._false), idIndices1))
      val assert = Assert(BinOp("&&", BinOp("=>", Const._true, BinOp("=>", eval(state.L.getOrElse(assign.lhs, Const._false), idIndices1), Gamma(assign.expression.variables))), Const._true)) // TODO
      val atomic = Atomic(List(assert, assume))
      (atomic, idIndices1)
    case ifStmt: If =>
      // 1: evaluate each branch separately (and maintain a list of modified vars)
      // 2: for each var introduce a new var with an index one higher then the max

      // If no else compare based on existing idindices

      val _test = eval(ifStmt.test, idIndices)
      var (_left: Block, idic1) = execute(ifStmt.left, idIndices, state)
      var (_right: Block, idic2) = ifStmt.right match {
        case Some(right: Block) => execute(right, idIndices, state)
        case None => (Block(List()), idIndices) // Need an empty block to add extra assumes
      }


      // Merge the two maps taking the max of the vals
      val _idIndices = idic1 ++ idic2.map{case (k, v) => k -> math.max(v, idic1.getOrElse(k, 0))}

      for ((k, v) <- _idIndices) {
        // TODO need ot handle var not declared before if
        if (idic1.getOrElse(k, 0) < v) {
          _left = _left.copy(statements = (_left.statements :+ Assume(BinOp("==", new Id(k, v), Id(k, idic1.getOrElse(k, 0))))))
        }


        if (idic2.getOrElse(k, 0) < v) {
          _right = _right.copy(statements = (_right.statements :+ Assume(BinOp("==", new Id(k, v), Id(k, idic2.getOrElse(k, 0))))))
        }
      }

      val _ifstmt = ifStmt.copy(test = _test, left = _left, right = Some(_right))
      // TODO: when merging from if do we need to add additional proof obligations

      (_ifstmt, idIndices)
    case block: Block =>
      val (stl, idi1) = execute(block.statements, idIndices, state)
      val block1 = block.copy(statements = stl)
      (block1, idi1)
    case stmt =>
      println("Unimplemented statement: " + stmt)
      (stmt, idIndices)
  }

  // TODO eval for expression
  def eval(expr: Expression, idIndices: Map[String, Int]): Expression = expr match {
    case id: Id =>
      id.copy(index = idIndices.getOrElse(id.name, 0))
    case id: Var =>
      Id(id.name, idIndices.getOrElse(id.name, 0))
    case BinOp(op, arg1, arg2) =>
      val _arg1 = eval(arg1, idIndices)
      val _arg2 = eval(arg2, idIndices)
      BinOp(op, _arg1, _arg2)
    case a: Lit => a
    case a: Const => a
    case expr =>
      println("Unimplemented expression: " + expr + " " + expr.getClass)
      expr
  }

  def updateVarIndex (id: Id, idIndices: Map[String, Int]): Map[String, Int] = {
    idIndices.updated(id.name, idIndices.getOrElse(id.name, -1) + 1)
  }
}
