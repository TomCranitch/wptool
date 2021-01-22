package wptool

import org.sosy_lab.java_smt._
import org.sosy_lab.java_smt.SolverContextFactory._

object SMT_ {
  val ctx = SolverContextFactory.createSolverContext(Solvers.SMTINTERPOL)
}
