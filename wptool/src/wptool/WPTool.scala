package wptool

import java.io.FileReader
import java.lang.ClassLoader
import java.net.URLClassLoader

import wptool.error._
import com.microsoft.z3
import scala.collection.mutable.ListBuffer

case class RG(
    program: String,
    rely: Expression,
    guarantee: Expression,
    arrayRs: Map[Id, Expression],
    guarRs: Map[Id, Expression]
) {}

object WPTool {
  var rgs: ListBuffer[RG] = ListBuffer()

  def main(args: Array[String]): Unit = {
    var toLog: Boolean =
      false // whether to print P/Gamma/D state information for each rule application
    var debug: Boolean = false // whether to print further debug information
    var noInfeasible: Boolean = false // whether to not check infeasible paths
    var simplify: Boolean =
      false // whether to output the simplified VC for failing VCs

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
        case "-s" =>
          simplify = true
        case _ =>
          val start = System.currentTimeMillis()
          try {
            println(run(file, debug, simplify))
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
              println(
                "Z3 Failed (this probably means there was an error in the input to Z3): " + e
              )
              printTime(start)
          }
      }

      if (!checkRGs(rgs.toList)) println("R/G do not agree")
    }
  }

  // TODO rm debug func
  def dispClassPath() = {
    def urlses(cl: ClassLoader): Array[java.net.URL] = cl match {
      case null                       => Array()
      case u: java.net.URLClassLoader => u.getURLs() ++ urlses(cl.getParent)
      case _                          => urlses(cl.getParent)
    }

    val urls = urlses(getClass.getClassLoader)
    println(urls.mkString("\n"))
  }

  def run(
      file: String,
      debug: Boolean,
      simplify: Boolean,
      silent: Boolean = false
  ): Boolean = {
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

    val state = State(variables, debug, silent, simplify, gamma_0, rely, guar)
    // printBlocks(PreProcess.process(statements, state))

    if (debug) PreProcess.printGraphvis(PreProcess.process(statements, state))

    val _state = Exec.exec(PreProcess.process(statements, state), state)

    rgs += new RG(
      file,
      rely.getOrElse(Rely(Const._true)).exp,
      guar.getOrElse(Guar(Const._true)).exp,
      _state.arrRelys,
      _state.arrGuars
    )

    val gammaDom: Set[Id] = _state.ids -- _state.arrayIds
    val gamma: Map[Id, Security] = gamma_0 match {
      // security high by default if user hasn't provided
      case None => Map()
      case Some(gs) =>
        {
          gs flatMap { g =>
            g.toPair
          }
        }.toMap
    }

    /*
    val gammaArraySubst = constructForall(
      _state.arrayIds
        .map(a =>
          ArrayConstDefault(
            a.toGamma.toVar(_state),
            gamma.getOrElse(a, High).toTruth
          )
        )
        .toList
    )
     */

    val gammaSubstr = {
      for (i <- gammaDom) yield {
        // i.toGamma.toVar(_state) -> Left(gamma.getOrElse(i, High).toTruth)
        // TODO TO TRUTH
        // TODO Low??
        Id.memId.toGamma.toVar(state) -> Right(Id.getAddr(i, state), gamma.getOrElse(i, Low).toTruth)
      }
    }.toMap ++ Map(Id.tmpId.toGamma.toVar(_state) -> Left(Const._true))

    // if (debug) println("Gamma0: " + gammaSubstr)
    if (debug) println("L: " + _state.L)
    if (debug) println("Indicies: " + _state.indicies)

    checkVcs(_state.Qs, gammaSubstr, debug, simplify) match {
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
      println(s"time: ${time / 1000}s ${time - (time / 1000) * 1000}ms")
    } else {
      println(s"time: ${time}ms")
    }
  }

  def parse(file: String): Global = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val result = parser.parse(scanner).asInstanceOf[Global]

    result
  }

  def printBlocks(block: Block): Unit = {
    println(block)
    block.children.foreach(b => printBlocks(b))
  }

  // TODO this is copy pasted
  def getRelyRec(exp: Expression): Option[Expression] = exp match {
    case BinOp(op, _, _, arg1, arg2) =>
      Some(constructForallOpt(getRelyRec(arg1), getRelyRec(arg2)))
    case PreOp(op, _, _, arg) => getRelyRec(arg)
    case i: Id                =>
      // TODO if global
      val id = i.getBase
      if (true) {
        Some(
          BinOp.pred(
            "=>",
            BinOp.pred("==", id, id.toPrime),
            BinOp.pred("==", id.toGamma, id.toPrime.toGamma)
          )
        )
      } else {
        Some(
          BinOp.pred(
            "&&",
            BinOp.pred("==", id, id.toPrime),
            BinOp.pred("==", id.toGamma, id.toPrime.toGamma)
          )
        )
      }
    case i: IdAccess =>
      val id = i.getBase
      if (true) {
        Some(
          BinOp.pred(
            "=>",
            BinOp.pred("==", id, id.toPrime),
            BinOp.pred("==", id.toGamma, id.toPrime.toGamma)
          )
        )
      } else {
        Some(
          BinOp.pred(
            "&&",
            BinOp.pred("==", id, id.toPrime),
            BinOp.pred("==", id.toGamma, id.toPrime.toGamma)
          )
        )
      }
    case s: VarStore =>
      getRelyRec(
        s.exp
      ) // TODO do we need it for arr and index as well? (similarly for eval)
    case _: Lit | _: Const => None
    case expr =>
      println(s"Unhandled expression(getRely): [${expr.getClass()}] $expr")
      None
  }

  def checkRGs(RGs: List[RG]): Boolean = {
    // TODO need to add in all the extra G1-G3

    RGs.foreach(r => {
      // Check main rely
      RGs.foreach(g => {
        if (
          r != g && !SMT.prove(
            BinOp.pred(
              "=>",
              BinOp.pred(
                "&&",
                g.guarantee,
                getRelyRec(r.rely).getOrElse(Const._true)
              ),
              r.rely
            ),
            false,
            false,
            true
          )
        ) {
          println(s"${g.guarantee} does not imply rely of ${r.rely}")
          println(s"    Additional constraints ${getRelyRec(r.rely)}")
          return false
        }
      })

      // Check array rely
      RGs.foreach(g => {
        if (r != g) {
          val cond = constructForall(g.guarRs.values.toList :+ g.guarantee)
          if (
            !SMT.prove(
              BinOp.pred(
                "=>",
                BinOp.pred("&&", cond, getRelyRec(r.rely).getOrElse(Const._true)),
                r.rely
              ),
              false,
              false,
              true
            )
          ) {
            println(s"${cond} does not imply rely of ${r.rely}")
            println(s"    Additional constraints ${getRelyRec(r.rely)}")
            return false
          }
        }
      })

      // TODO this cannot handle the case arrR: a[_i] > 10, R: a[0] > 10
      // think about this a bit more but this particular example is bad
      // i think its would fail with arrG: a[_i] > 10 and arrR: a[0] > 10 (this would pass with (_i == 0) => (a[0] > 10))
    })
    return true
  }
}
