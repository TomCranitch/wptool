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

  def run (file: String, debug: Boolean): Boolean = {
    val res = parse(file)
    val variables = res.variables

    val statements = res.statements
    val P_0 = res.P_0
    val gamma_0 = res.gamma_0
    if (debug) {
      println(statements)
      println(variables)
      println(P_0)
      println(gamma_0)
    }

    val state = State(variables, debug, gamma_0)
    val (passifiedStmts, _) = Passify.execute(statements, PassifyState(state, gamma_0, variables))


    val _state = Exec.exec(passifiedStmts, state)

    SMT.prove(_state.Q, List[Expression](), debug = false)
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



}
