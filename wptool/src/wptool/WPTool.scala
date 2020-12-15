package wptool

import java.io.FileReader
import java.lang.ClassLoader
import java.net.URLClassLoader

import wptool.error._
import com.microsoft.z3

object WPTool {

  def main(args: Array[String]): Unit = {
    var toLog: Boolean = false // whether to print P/Gamma/D state information for each rule application
    var debug: Boolean = false // whether to print further debug information
    var noInfeasible: Boolean = false // whether to not check infeasible paths

    if (args.isEmpty) {
      println("usage: ./wptool.sh file1 file2...")
    } else {
      for (file <- args) file match {
        case "-v" =>
          toLog = true
        case "-d" =>
          debug = true
          toLog = true
        case "-p" =>
          noInfeasible = true
        case _ =>
          val start = System.currentTimeMillis()
          try {
            println(run(file, debug))
            printTime(start)
          } catch {
            case e: java.io.FileNotFoundException =>
              println("file does not exist")
            case e: InvalidProgram =>
              println("invalid input file: " + e)
              printTime(start)
            case e: ProgramError =>
              println("internal error: " + e)
              printTime(start)
            case e: Z3Error =>
              println("Z3 Failed (this probably means there was an error in the input to Z3): " + e)
              printTime(start)
            case e @ (_: WhileError | _: IfError | _: AssignCError | _: AssignError | _: NonblockingError | _: CASCError | _: CASError | _: ArrayError | _: ArrayCError) =>
              println(e)
              printTime(start)
          }
      }
    }
  }


  // TODO rm debug func
  def dispClassPath () = {
    def urlses(cl: ClassLoader): Array[java.net.URL] = cl match {
      case null => Array()
      case u: java.net.URLClassLoader => u.getURLs() ++ urlses(cl.getParent)
      case _ => urlses(cl.getParent)
    }

    val urls = urlses(getClass.getClassLoader)
    println(urls.mkString("\n"))
  }

  def run (file: String, debug: Boolean, silent: Boolean = false): Boolean = {
    val res = parse(file)
    val variables = res.variables

    val statements = res.statements
    val P_0 = res.P_0
    val gamma_0 = res.gamma_0
    val rely = res.rely
    val guar = res.guarantee
    if (debug) {
      println(statements)
      println(variables)
      println(P_0)
      println(gamma_0)
      println(rely)
      println(guar)
    }

    val state = State(variables, debug, gamma_0, rely, guar)
    // printBlocks(PreProcess.process(statements, state))

    if (debug) PreProcess.printGraphvis(PreProcess.process(statements, state))

    val _state = Exec.exec(PreProcess.process(statements, state), state)


    val gammaDom: Set[Id] = _state.ids
    val gamma: Map[Id, Security] = gamma_0 match {
      // security high by default if user hasn't provided
      case None => Map()
      case Some(gs) => {
        gs flatMap {g => g.toPair}
      }.toMap
    }
    val gammaSubstr = {
      for (i <- gammaDom) yield {
        i.toGamma.toVar(_state) -> gamma.getOrElse(i, High).toTruth
      }
    }.toMap[Var, Expression] ++ Map(Id.tmpId.toGamma.toVar(_state) -> Const._true)

    //if (debug) println("VCs: " + vcs)
    if (debug) println("Gamma0: " + gammaSubstr)
    if (debug) println("L: " + _state.L)
    if (debug) println("Indicies: " + _state.indicies)

    checkVcs(_state.Qs, gammaSubstr, debug) match {
      case Some(s) =>
        if (!silent) printFalseVcs(s)
        false
      case None => 
        if (_state.error) false
        else true
    }
  }

  def printTime(start: Long): Unit = {
    val end = System.currentTimeMillis()
    val time = end - start
    if (time >= 1000) {
      println("time: " + (time / 1000) + "s")
    } else {
      println("time: " + time + "ms")
    }
  }

  def parse(file: String): Global = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val result = parser.parse(scanner).asInstanceOf[Global]

    result
  }

  def printBlocks (block: Block): Unit = {
    println(block)
    block.children.foreach(b => printBlocks(b))
  }


}
