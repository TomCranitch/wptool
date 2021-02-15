package wptool

import org.sosy_lab.java_smt._
import org.sosy_lab.java_smt.SolverContextFactory._
import org.sosy_lab.java_smt.api.FormulaType
import scala.reflect.runtime.universe.{TypeTag, typeOf}
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType

object SMT {
  type array = api.ArrayFormula[api.NumeralFormula.IntegerFormula, _ <: api.Formula]
  val solver = Solvers.CVC4
  val ctx = SolverContextFactory.createSolverContext(solver)
  val fmgr = ctx.getFormulaManager();
  val bmgr = fmgr.getBooleanFormulaManager();
  val imgr = fmgr.getIntegerFormulaManager();
  val amgr = fmgr.getArrayFormulaManager();

  def prove(
      cond: Expression,
      debug: Boolean,
      simplify: Boolean,
      expectIds: Boolean = false
  ): Boolean = {
    if (debug)
      println("smt checking !(" + cond + ")")

    // solver.push()
    val prover = ctx.newProverEnvironment(ProverOptions.GENERATE_MODELS)

    val res =
      try {
        // check that (NOT cond) AND P is unsatisfiable
        prover.addConstraint(translateBool(PreOp("!", TBool, TBool, cond), expectIds))

        return prover.isUnsat();

      } catch {
        case e: Throwable =>
          throw e
      }

    /*
    if (debug) {
      println(res)
      if (res == z3.Status.SATISFIABLE) {
        val model = solver.getModel
        println(
          "Model: [" + cond.vars.toList
            .sortWith((x, y) => x.toString < y.toString)
            .map(x => x + " -> " + model.eval(translate(x, expectIds), false))
            .mkString(", ") + "]"
        )
      }
      // println(solverSimplify(cond, true))
    }
    res == z3.Status.UNSATISFIABLE
     */

    return false;
  }

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

  def getArray(store: Expression): api.ArrayFormula[api.NumeralFormula.IntegerFormula, _ <: api.Formula] = store match {
    case a: VarAccess =>
      if (a.expType == TBool) {
        amgr.makeArray[api.NumeralFormula.IntegerFormula, api.BooleanFormula, api.FormulaType[
          api.NumeralFormula.IntegerFormula
        ], api.FormulaType[api.BooleanFormula]](
          a.name.toString,
          FormulaType.IntegerType,
          FormulaType.BooleanType
        )
      } else {
        amgr.makeArray[api.NumeralFormula.IntegerFormula, api.NumeralFormula.IntegerFormula, api.FormulaType[
          api.NumeralFormula.IntegerFormula
        ], api.FormulaType[api.NumeralFormula.IntegerFormula]](
          a.name.toString,
          FormulaType.IntegerType,
          FormulaType.IntegerType
        )
      }
    case a: VarStore => getArray(a.array)
    case _           => throw new Error("Unexpected statement in VarStore")
  }

  def makeSelect(
      id: String,
      index: Expression,
      isBool: Boolean,
      expectIds: Boolean
  ): api.Formula = {
    amgr
      .select(
        makeArray(id, isBool).asInstanceOf[array],
        translateInt(index, expectIds)
      )
  }

  def handleSelect(
      store: Expression,
      arr: array,
      expectIds: Boolean
  ): api.Formula = store match {
    case a: VarAccess => makeSelect(a.ident.toString, a.index, a.expType == TBool, expectIds)
    case a: VarStore  => handleSelect(a.array, arr, expectIds)
    case _            => throw new Error("Unexpected statement in VarStore")
  }

  def handleStore(
      store: Expression,
      expectIds: Boolean,
      arrType: Type
  ): array = {
    store match {
      case a: VarAccess =>
        makeArray(a.ident.toString, a.ident.expType == TBool)
          .asInstanceOf[array]
      case a: VarStore =>
        if (a.expType != arrType) throw new Error(s"Actual (${a.expType}) and expect (${arrType}) array type do not match for $a")
        amgr.store(
          handleStore(a.array, expectIds, arrType).asInstanceOf[api.ArrayFormula[api.NumeralFormula.IntegerFormula, api.Formula]],
          translateInt(a.index, expectIds),
          a.expType match {
            case TInt  => translateInt(a.exp, expectIds)
            case TBool => translateBool(a.exp, expectIds)
            case _     => throw new Error("Unexpected type")
          }
        )
      case _ => throw new Error("Unexpected statement in VarStore")
    }
  }

  def translateBool(prop: Expression, expectIds: Boolean): api.BooleanFormula = prop match {
    case Const._true  => bmgr.makeTrue
    case Const._false => bmgr.makeFalse

    case BinOp("==", TBool, TBool, arg1, arg2) =>
      bmgr.equivalence(translateBool(arg1, expectIds), translateBool(arg2, expectIds))
    case BinOp("!=", TBool, TBool, arg1, arg2) =>
      bmgr.not(
        bmgr.equivalence(translateBool(arg1, expectIds), translateBool(arg2, expectIds))
      )

    case PreOp("!", TBool, TBool, arg) => bmgr.not(translateBool(arg, expectIds))
    case BinOp("&&", TBool, TBool, arg1, arg2) =>
      bmgr.and(translateBool(arg1, expectIds), translateBool(arg2, expectIds))
    case BinOp("||", TBool, TBool, arg1, arg2) =>
      bmgr.or(translateBool(arg1, expectIds), translateBool(arg2, expectIds))
    case BinOp("=>", TBool, TBool, arg1, arg2) =>
      bmgr.implication(translateBool(arg1, expectIds), translateBool(arg2, expectIds))

    case BinOp("==", TInt, TBool, arg1, arg2) =>
      imgr.equal(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp("!=", TInt, TBool, arg1, arg2) =>
      bmgr.not(
        imgr.equal(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
      )

    case BinOp("<=", TInt, TBool, arg1, arg2) =>
      imgr.lessOrEquals(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp("<", TInt, TBool, arg1, arg2) =>
      imgr.lessThan(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp(">=", TInt, TBool, arg1, arg2) =>
      imgr.greaterOrEquals(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp(">", TInt, TBool, arg1, arg2) =>
      imgr.greaterThan(translateInt(arg1, expectIds), translateInt(arg2, expectIds))

    case v @ Var(Id(_, TBool, _, _, _), _, _) if (!expectIds) => bmgr.makeVariable(v.toString)
    case v @ Id(_, TBool, _, _, _) if (expectIds)             => bmgr.makeVariable(v.toString)
    // TODO refactor to use Type not bool for isBoolean
    case x: VarAccess if (!expectIds && x.expType == TBool) =>
      makeSelect(x.name.toString, x.index, true, expectIds).asInstanceOf[api.BooleanFormula]
    case x: IdAccess if (expectIds && x.expType == TBool) =>
      makeSelect(x.ident.toString, x.index, true, expectIds).asInstanceOf[api.BooleanFormula]
    case store: VarStore =>
      handleSelect(store.array, handleStore(store, expectIds, TBool), expectIds).asInstanceOf[api.BooleanFormula]

    case _ => throw new Error(s"Unexpected boolean expression $prop")
  }

  def translateInt(prop: Expression, expectIds: Boolean): api.NumeralFormula.IntegerFormula = prop match {
    case Lit(n: Int) => imgr.makeNumber(n)

    case Var(Id.indexId, _, _) => throw new Error("Unsubstituted index")
    case BinOp("%", TInt, TInt, arg1, arg2) =>
      imgr.modulo(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp("+", TInt, TInt, arg1, arg2) =>
      imgr.add(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp("-", TInt, TInt, arg1, arg2) =>
      imgr.subtract(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp("*", TInt, TInt, arg1, arg2) =>
      imgr.multiply(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case BinOp("/", TInt, TInt, arg1, arg2) =>
      imgr.divide(translateInt(arg1, expectIds), translateInt(arg2, expectIds))
    case PreOp("-", TInt, TInt, arg) => imgr.negate(translateInt(arg, expectIds))
    case PreOp("+", TInt, TInt, arg) => translateInt(arg, expectIds)

    // TODO *+-/

    case v @ Var(Id(_, TInt, _, gamma, _), _, _) if (!expectIds && !gamma) => imgr.makeVariable(v.toString)
    case v @ Id(_, TInt, _, gamma, _) if (expectIds && !gamma)             => imgr.makeVariable(v.toString)
    // TODO maybe this is the wrong type?
    case x: VarAccess if (!expectIds && x.expType == TInt) =>
      makeSelect(x.name.toString, x.index, false, expectIds).asInstanceOf[api.NumeralFormula.IntegerFormula]
    case x: IdAccess if (expectIds && x.expType == TInt) =>
      makeSelect(x.ident.toString, x.index, false, expectIds).asInstanceOf[api.NumeralFormula.IntegerFormula]

    case store: VarStore =>
      handleSelect(store.array, handleStore(store, expectIds, TInt), expectIds).asInstanceOf[api.NumeralFormula.IntegerFormula]

    /*

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

    case _ =>
      throw new Error(s"Unexpected integer expression $prop")
  }
}
