package wptool

import reflect.runtime.universe.{typeOf}

object PreProcess {
  def process(statements: List[Stmt], state: State): Block = {
    Block.resetNames
    val _statements = exec(statements, state, Block("END", List(), List()))
    removeLoops(_statements, state)
  }

  /**  Convert a while program into basic blocks
    */
  // @scala.annotation.tailrec
  private def exec(
      statements: List[Stmt],
      state: State,
      currBlock: Block
  ): Block = statements match {
    case rest :+ last =>
      val block = exec(last, state, currBlock)
      exec(rest, state, block)
    case Nil => currBlock
  }

  private def exec(block: Block, state: State, currBlock: Block): Block = exec(block.statements, state, currBlock)

  private def exec(stmt: Stmt, state: State, currBlock: Block): Block =
    stmt match {
      // TODO to get types for evalExp need to perform a match
      case assign: Assignment =>
        // TODO typeOf(assign) // TODO
        evalBlock(
          assign.expression,
          currBlock.prepend(
            assign.copy(expression = evalExp(assign.expression))
          )
        )
      case assign: ArrayAssignment =>
        evalBlock(
          assign.expression,
          currBlock.prepend(
            assign.copy(expression = evalExp(assign.expression))
          )
        )
      case assert: Assert => currBlock.prepend(assert)
      case ifStmt: If     =>
        // val goto = ifStmt.
        // Parse to if (...) goto ...
        // when setting path into c1, set c1 to have the parent (as opposed to the parent having the child) this will make going back easier
        val test = evalExp(ifStmt.test)
        val left = exec(
          ifStmt.left,
          state,
          Block("if left", List(), List(currBlock))
        ).prepend(Guard(test))
        val right = ifStmt.right match {
          case Some(s) =>
            exec(s, state, Block("if right", List(), List(currBlock)))
              .prepend(Guard(PreOp("!", TBool, TBool, test)))
          case None =>
            Block(
              "if empty",
              List(Guard(PreOp("!", TBool, TBool, test))),
              List(currBlock)
            )
        }
        evalBlock(ifStmt.test, Block("pre if", List(), List(left, right)))
      case whileStmt: While =>
        val after =
          currBlock.prepend(Assume(PreOp("!", TBool, TBool, evalExp(whileStmt.test))))
        // TODO why does the body not go to after ?? (as per paper/PASTE05)
        val body =
          Block("while body", List(Assert(whileStmt.invariant)), List())
        val _body = exec(whileStmt.body, state, body)
          .prepend(Guard(evalExp(whileStmt.test)))
        val inv = whileStmt.invariant

        val head = evalBlock(
          whileStmt.test,
          (Block("while head", List(), List(_body, after)))
        ).prepend(Assume(whileStmt.invariant))
          .prepend(Havoc())
          .prepend(Assert(whileStmt.invariant, true))
        // Assert(branchGamma)
        head
      case doWhile: DoWhile =>
        val after = currBlock.prepend(Assume(PreOp("!", TBool, TBool, evalExp(doWhile.test))))
        val repeat = Block(
          "do-while repeat",
          List(Guard(doWhile.test), Assert(doWhile.invariant, true)),
          List()
        )
        val block = Block("do-while block", List(), List(after, repeat))
        exec(doWhile.body, state, block)
          .prepend(Assume(doWhile.invariant))
          .prepend(Havoc())
          .prepend(Assert(doWhile.invariant))
      case _ =>
        println("Unhandled statement (preprocessor): " + stmt)
        currBlock.prepend(Malformed)
    }

  def evalBlock(exp: Expression, currBlock: Block): Block = exp match {
    case cas: CompareAndSwap =>
      val left = Block(
        "cas left",
        List(
          Guard(BinOp("==", TInt, TBool, cas.x, cas.e1)),
          Assignment(cas.x, cas.e2),
          Assignment(Id.tmpId, Lit(1))
        ),
        List(currBlock),
        true
      )
      val right = Block(
        "cas right",
        List(
          Guard(BinOp("!=", TInt, TBool, cas.x, cas.e1)),
          Assignment(Id.tmpId, Lit(0))
        ),
        List(currBlock),
        true
      )
      val before = Block("before cas", List(), List(left, right))
      before
    case BinOp(_, _, _, _, _: CompareAndSwap) =>
      throw new Error("currently unsupported")
    case BinOp(op, _, _, arg1, arg2) =>
      evalBlock(arg1, evalBlock(arg2, currBlock)) // TODO
    // TODO binop
    case PreOp(op, _, _, arg) => evalBlock(arg, currBlock)
    case _                    => currBlock
  }

  def evalExp(exp: Expression): Expression = exp match {
    case cas: CompareAndSwap           => Id.tmpId
    case BinOp(op, t1, t2, arg1, arg2) => BinOp(op, t1, t2, evalExp(arg1), evalExp(arg2))
    case PreOp(op, t1, t2, arg)        => PreOp(op, t1, t2, evalExp(arg))
    case _                             => exp
  }

  def removeLoops(block: Block, state: State) = {
    // Begin by convering to reducible graph (this is not necassary for whiles ??)
    // First, detect loops (cycle finding)
    // Then, apply logic given in paper (PASTE05??)

    // Currently, this can be avoided by doing the conversion when the while statement is processed
    block
  }

  def printGraphvis(block: Block): Unit = {
    println("digraph G {")
    println("node [style=filled,color=white]")
    printGraphvis(block, "START", Set())
    println("}")
  }

  def printGraphvis(
      block: Block,
      parent: String,
      visitedNodes: Set[String]
  ): Set[String] = {
    println(parent + " -> " + block.name + "0")

    if (visitedNodes.contains(block.name)) return visitedNodes;
    val _visitedNodes = visitedNodes + block.name

    printBlock(block)
    // TODO changed parents to children. need to fix
    block.children.foldLeft(_visitedNodes) { (s, b) =>
      printGraphvis(
        b,
        block.name + math.max((block.statements.length - 1), 0),
        s
      )
    }
  }

  def printBlock(block: Block): Unit = {
    println("subgraph cluster_" + block.name + " {")
    println(s"""label = "${block.name} (${block.label})";""")
    for ((i, s) <- block.statements.indices.zip(block.statements))
      println(s"""${block.name}${i} [label = \"${s.getLine._2}: ${s.toString}"];""")
    if (block.statements.length > 0)
      println(
        block.statements.indices.map(i => block.name + i).mkString(" -> ") + ";"
      )
    println("}")

  }

}
