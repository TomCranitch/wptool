package wptool

import org.sosy_lab.java_smt._
import org.sosy_lab.java_smt.SolverContextFactory._
import org.sosy_lab.java_smt.api.FormulaType

object SMT_ {
  val ctx = SolverContextFactory.createSolverContext(Solvers.SMTINTERPOL)
  val fmgr = ctx.getFormulaManager();
  val bmgr = fmgr.getBooleanFormulaManager();
  val imgr = fmgr.getIntegerFormulaManager();
  val amgr = fmgr.getArrayFormulaManager();

  def makeArray(id: String, isBool: Boolean): api.ArrayFormula[api.NumeralFormula.IntegerFormula, _ <: api.Formula] = {
    if (isBool) {
      amgr.makeArray[api.NumeralFormula.IntegerFormula, api.BooleanFormula, api.FormulaType[
        api.NumeralFormula.IntegerFormula
      ], api.FormulaType[api.BooleanFormula]](
        id,
        FormulaType.IntegerType,
        FormulaType.BooleanType
      )
    } else {
      amgr.makeArray[api.NumeralFormula.IntegerFormula, api.NumeralFormula.IntegerFormula, api.FormulaType[
        api.NumeralFormula.IntegerFormula
      ], api.FormulaType[api.NumeralFormula.IntegerFormula]](
        id,
        FormulaType.IntegerType,
        FormulaType.IntegerType
      )
    }
  }

  def makeSelect(
      id: String,
      index: Expression,
      isBool: Boolean,
      expectIds: Boolean
  ) =
    amgr.select(
      makeArray(id, isBool).asInstanceOf[api.ArrayFormula[api.Formula, _ <: api.Formula]],
      translate(index, expectIds)
    )

  def arith(prop: Expression, expectIds: Boolean): api.NumeralFormula.IntegerFormula = prop match {
    case PreOp("-", arg) => imgr.negate(arith(arg, expectIds))
    case BinOp("+", arg1, arg2) =>
      imgr.add(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("-", arg1, arg2) =>
      imgr.subtract(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("*", arg1, arg2) =>
      imgr.multiply(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("/", arg1, arg2) =>
      imgr.divide(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("%", arg1, arg2) =>
      imgr.modulo(arith(arg1, expectIds), arith(arg2, expectIds))
  }

  def arithBool(prop: Expression, expectIds: Boolean): api.BooleanFormula = prop match {
    case BinOp("==", arg1, arg2) =>
      imgr.equal(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("!=", arg1, arg2) =>
      bmgr.not(
        imgr.equal(arith(arg1, expectIds), arith(arg2, expectIds))
      )

    case BinOp("<=", arg1, arg2) =>
      imgr.lessOrEquals(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("<", arg1, arg2) =>
      imgr.lessThan(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp(">=", arg1, arg2) =>
      imgr.greaterOrEquals(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp(">", arg1, arg2) =>
      imgr.greaterThan(arith(arg1, expectIds), arith(arg2, expectIds))

  }

  def formula(prop: Expression, expectIds: Boolean): api.BooleanFormula = prop match {
    // Check equal and equivalence are the same
    case BinOp("==", arg1, arg2) =>
      bmgr.equivalence(formula(arg1, expectIds), formula(arg2, expectIds))
    case BinOp("!=", arg1, arg2) =>
      bmgr.not(
        bmgr.equivalence(formula(arg1, expectIds), formula(arg2, expectIds))
      )

    case PreOp("!", arg) => bmgr.not(formula(arg, expectIds))
    case BinOp("&&", arg1, arg2) =>
      bmgr.and(formula(arg1, expectIds), formula(arg2, expectIds))
    case BinOp("||", arg1, arg2) =>
      bmgr.or(formula(arg1, expectIds), formula(arg2, expectIds))

    case BinOp("=>", arg1, arg2) =>
      bmgr.implication(formula(arg1, expectIds), formula(arg2, expectIds))

  }

  def translate(prop: Expression, expectIds: Boolean): api.Formula = prop match {
    case Const._true  => bmgr.makeTrue
    case Const._false => bmgr.makeFalse

    case Lit(n: Int) => imgr.makeNumber(n)

    case Var(Id.indexId, _, _) => throw new Error("Unsubstituted index")
    case x: Var =>
      if (expectIds) throw new Error("Program ids should not be resolved")
      if (x.ident.gamma) bmgr.makeVariable(x.toString)
      else imgr.makeVariable(x.toString)
    case x: Id =>
      if (!expectIds) throw new Error("unresolved id")
      if (x.gamma) bmgr.makeVariable(x.toString)
      else imgr.makeVariable(x.toString)

    // TODO can these cases be merged together
    case x: VarAccess =>
      if (expectIds) throw new Error("Program ids should not be resolved")
      makeSelect(x.name.toString, x.index, x.ident.gamma, expectIds)
    case x: IdAccess =>
      if (!expectIds) throw new Error("unresolved array id")
      makeSelect(x.ident.toString, x.index, x.ident.gamma, expectIds)

    /*
    case store: VarStore =>
      handleStore(
        store,
        getArray(store),
        expectIds
      )

    case const: ArrayConstDefault =>
      // TODO i dont think this is correct (https://stackoverflow.com/questions/54863754/z3-set-default-value-of-array-to-zero)
      if (const.name.ident.gamma)
        ctx.mkEq(
          ctx
            .mkArrayConst(const.name.toString, ctx.getIntSort, ctx.getBoolSort),
          ctx.mkConstArray(ctx.getIntSort, translate(const.const, expectIds))
        )
      else throw new Error("ArrayConstDefault is only for gamma values")

     */

    /*

    case BinOp("|", arg1, arg2) =>
      ctx.mkBVOR(bitwise(arg1, expectIds), bitwise(arg2, expectIds))
    case BinOp("&", arg1, arg2) =>
      ctx.mkBVAND(bitwise(arg1, expectIds), bitwise(arg2, expectIds))
    case BinOp("^", arg1, arg2) =>
      ctx.mkBVXOR(bitwise(arg1, expectIds), bitwise(arg2, expectIds))
    case PreOp("~", arg) => ctx.mkBVNot(bitwise(arg))

    // defining normal right shift as logical shift right
    case BinOp(">>", arg1, arg2) =>
      ctx.mkBVLSHR(bitwise(arg1, expectIds), bitwise(arg2, expectIds))
    case BinOp(">>>", arg1, arg2) =>
      ctx.mkBVASHR(bitwise(arg1, expectIds), bitwise(arg2, expectIds))
    case BinOp("<<", arg1, arg2) =>
      ctx.mkBVSHL(bitwise(arg1, expectIds), bitwise(arg2, expectIds))

    case Question(test, arg1, arg2) =>
      ctx.mkITE(
        formula(test, expectIds),
        translate(arg1, expectIds),
        translate(arg2, expectIds)
      )

    // boundConstraints, body, 0, scala.Arry(), null, null, null
    case ForAll(bound, body) =>
      ctx.mkForall(
        bound.toArray.map(b => translate(b, expectIds)),
        translate(body, expectIds),
        0,
        scala.Array(),
        null,
        null,
        null
      )
     */

    /*
    case Exists(bound, body) =>
      ctx.mkExists(bound.toArray map translate, translate(body), 0, scala.Array(), null, null, null)
     */

    case _ =>
      throw new Error(s"cannot translate to SMT $prop")
  }
}
