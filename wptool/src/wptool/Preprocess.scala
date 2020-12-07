package wptool

object PreProcess {
  def process (statements: List[Statement], state: State): Block = {
    val _statements = exec(statements, state, new Block("START", List(), List()))
    removeLoops(_statements, state)
  }


  /**
   *  Convert a while program into basic blocks 
   **/
  // @scala.annotation.tailrec
  private def exec (statements: List[Statement], state: State, currBlock: Block): Block = statements match {
      case rest :+ last =>
        val block = exec(last, state, currBlock)
        exec(rest, state, block)
      case Nil => currBlock
  }

  private def exec (stmt: Statement, state: State, currBlock: Block): Block = stmt match {
    case block: Block =>
      // TODO incorrect
      exec(block.statements, state, currBlock)
    case _: Assignment => currBlock.prepend(stmt)
    case ifStmt: If => 
      // val goto = ifStmt.
      // Parse to if (...) goto ...
      // when setting path into c1, set c1 to have the parent (as opposed to the parent having the child) this will make going back easier
      val left = exec(ifStmt.left, state, new Block("if left", List(), List(currBlock))).prepend(Guard(ifStmt.test))
      val right = ifStmt.right match {
        case Some(s) =>
          exec(s, state, new Block("if right", List(), List(currBlock))).prepend(Guard(PreOp("!", ifStmt.test)))
        case None =>
          new Block("if empty", List(Guard(PreOp("!", ifStmt.test))), List(currBlock))
      }
      val first = new Block("pre if", List(), List(left, right))
      first
    case whileStmt: While => 
      val after = currBlock.prepend(Assume(PreOp("!", whileStmt.test)))
      val body = new Block("while body", List(Assert(whileStmt.invariant)), List(after))
      val _body =  exec(whileStmt.body, state, body).prepend(Guard(whileStmt.test))
      // val branchGamma = computeGamma(whileStmt.test.vars.toList, state)
      val inv = whileStmt.invariant // TODO
      val head = new Block("while head", List(
        Assert(whileStmt.invariant, true),
        Havoc(),
        Assume(whileStmt.invariant),
        // Assert(branchGamma)
      ), List(body))
      head
    case _ => 
      println("Unhandled statement (preprocessor): " + stmt)
      currBlock.prepend(Malformed)
  }

  def removeLoops (block: Block, state: State) = {
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

  def printGraphvis (block: Block, parent: String, visitedNodes: Set[String]): Set[String] = {
    println(parent + " -> " + block.name + "0")

    if (visitedNodes.contains(block.name)) return visitedNodes;
    val _visitedNodes = visitedNodes + block.name

    printBlock(block)
    // TODO changed parents to children. need to fix
    block.children.foldLeft(_visitedNodes) {(s, b) => printGraphvis(b, block.name + (block.statements.length - 1), s)}
  }

  def printBlock (block: Block): Unit = {
    println("subgraph cluster_" + block.name + " {")
    println(s"""label = "${block.name} (${block.label})";""")
    for ((i, s) <- block.statements.indices.zip(block.statements)) println(s"""${block.name}${i} [label = \"${s.toString}"];""")
    if (block.statements.length > 0) println(block.statements.indices.map(i => block.name + i).mkString(" -> ") +";")
    println("}")

  }

}
