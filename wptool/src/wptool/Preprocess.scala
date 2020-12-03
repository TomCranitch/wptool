package wptool

object PreProcess {
  def process (statements: List[Statement], state: State): Block = {
    val _statements = exec(statements, state, Block("START", List(), List()))
    removeLoops(_statements, state)
  }


  /**
   *  Convert a while program into basic blocks 
   **/
  // @scala.annotation.tailrec
  def exec (statements: List[Statement], state: State, currBlock: Block): Block = statements match {
      case first :+ rest =>
        val block = exec(first, state, currBlock)
        exec(rest, state, block)
      case Nil => currBlock
  }

  def exec (stmt: Statement, state: State, currBlock: Block): Block = stmt match {
    case block: Block =>
      // TODO incorrect
      exec(block.statements, state, Block(block.name, List(), List(currBlock)))
    case _: Assignment => currBlock.append(stmt)
    case ifStmt: If => 
      // val goto = ifStmt.
      // Parse to if (...) goto ...
      // when setting path into c1, set c1 to have the parent (as opposed to the parent having the child) this will make going back easier
      val _currBlock = currBlock.append(Goto())
      // TODO Fix to add assume to the same block
      val left = exec(ifStmt.left.statements, state, Block("if left", List(Assume(ifStmt.test)), List(_currBlock))).append(Goto())
      val right = ifStmt.right match {
        case Some(s) =>
          exec(s.statements, state, Block("if right", List(Assume(PreOp("!", ifStmt.test))), List(_currBlock))).append(Goto())
        case None =>
          Block("if empty", List(Assume(PreOp("!", ifStmt.test)), Goto()), List(_currBlock))
      }
      val finalBlock = Block("post if", List(), List(left, right))
      // println("Unhandled statement (preprocessor) if: " + stmt)
      finalBlock
    case whileStmt: While => 
      println("Unhandled statement (preprocessor) while: " + stmt)
      currBlock
    case _ => 
      println("Unhandled statement (preprocessor): " + stmt)
      currBlock.append(Malformed)
  }

  def removeLoops (block: Block, state: State) = {
    // Begin by convering to reducible graph (this is not necassary for whiles ??)
    // First, detect loops (cycle finding)
    // Then, apply logic given in paper (PASTE05??)
    
    // Currently, this can be avoided by doing the conversion when the while statement is processed
    block
  }

}
