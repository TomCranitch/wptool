package object wptool {
  object error {

    abstract class Error extends Exception {
      def info: Seq[Any]

      override def toString = info.mkString(" ")
    }

    case class InvalidProgram(info: Any*) extends Error
    case class ProgramError(info: Any*) extends Error
    case class Z3Error(info: Any*) extends Error
  }

  // TODO this doesnt feel like the best way to do this
  // Either[substitution, (index, substitution)]
  type Subst = Map[Var[_ <: Type], Either[Expression[_ <: Type], (Expression[TInt], Expression[_ <: Type])]]

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      if (index < 0) self + "__" + index
      else self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None        => self
      case Some(index) => this __ index
    }

    def arrayIndex(index: Int): String = self + "[" + index + "]"

  }

  val newline = """
      |""".stripMargin

  implicit class PToString(P: List[Expression[TBool]]) {
    def PStr: String = P.mkString(" &&" + newline + "   ")
  }

  implicit class GammaToString(gamma: Map[Id[TBool], Security]) {
    def gammaStr = gamma.mkString(", ")
  }

  def constructMutliOp(op: String, exprs: List[Expression[TBool]]): Expression[TBool] =
    exprs match {
      case expr :: Nil => expr
      case expr :: rest =>
        BinOp(op, expr, constructForall(rest))
      case Nil => Const._true
    }

  def constructForall(exprs: List[Expression[TBool]]): Expression[TBool] = exprs match {
    case expr :: Nil => expr
    case expr :: rest =>
      BinOp("&&", expr, constructForall(rest))
    case Nil => Const._true
  }
  def constructForallOpt(exprs: List[Option[Expression[TBool]]]): Expression[TBool] =
    exprs match {
      case Some(expr) :: Nil  => expr
      case None :: Nil        => Const._true
      case Some(expr) :: rest => BinOp("&&", expr, constructForallOpt(rest))
      case None :: rest       => constructForallOpt(rest)
      case Nil                => Const._true
    }

  def constructForall(exprs: Expression[TBool]*): Expression[TBool] =
    constructForall(exprs.toList)
  def constructForallOpt(exprs: Option[Expression[TBool]]*): Expression[TBool] =
    constructForallOpt(exprs.toList)

  def checkVcs(
      preds: List[PredInfo],
      debug: Boolean,
      simplify: Boolean
  ): Option[List[PredInfo]] =
    preds.filter(p => {
      if (debug) println(s"passing ${p.stmt.toStringWLine} ${p.label} along path ${p.path.mkString(", ")} to SMT")
      !SMT.prove(p.pred, List(), debug, simplify)
    }) match {
      case List() => None
      case l      => Some(l)
    }

  def checkVcs(
      preds: List[PredInfo],
      gammas: Subst,
      debug: Boolean,
      simplify: Boolean
  ): Option[List[PredInfo]] =
    checkVcs(
      preds.map(p => {
        p.copy(pred = p.pred.subst(gammas))
      }),
      debug,
      simplify
    )

  def checkVcs(
      preds: List[PredInfo],
      gammas: Subst,
      arrayGamma: Expression[TBool],
      debug: Boolean,
      simplify: Boolean
  ): Option[List[PredInfo]] =
    checkVcs(
      preds.map(p => {
        p.copy(pred = BinOp("=>", arrayGamma, p.pred.subst(gammas)))
      }),
      debug,
      simplify
    )

  def printFalseVcs(preds: List[PredInfo]) = {
    println("Failing VCs")
    preds.foreach(p => {
      println(s"  ${p.stmt.toStringWLine}: ${p.label} along path ${p.path.mkString(", ")}")
      println(s"    ${p.pred}")
    })
  }

}
