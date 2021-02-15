package wptool

import com.microsoft.z3
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.enumerations.Z3_decl_kind
import scala.reflect.runtime.universe.{TypeTag, typeOf}

object SMT_ {
  val intSize = 32 // size of bitvectors used
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver = ctx.mkSolver()

  def solverSimplify(cond: Expression, fast: Boolean) = {
    val g = ctx.mkGoal(true, false, false)
    g.add(formula(cond))
    // ctx.mkTactic(if (fast) "simplify" else "ctx-solver-simplify").apply(g)
    ctx.mkTactic("simplify").apply(g)
    // ctx.mkTactic("solve-eqs").apply(g)
  }

  def prove(
      cond: Expression,
      debug: Boolean,
      simplify: Boolean,
      expectIds: Boolean = false
  ) = {
    if (debug) {
      println("smt checking !(" + cond + ")")
      println("translated as " + formula(PreOp("!", TBool, TBool, cond), expectIds))
    }

    solver.push()
    val res =
      try {
        // check that (NOT cond) AND P is unsatisfiable
        solver.add(formula(PreOp("!", TBool, TBool, cond), expectIds))

        solver.check
      } catch {
        case e: java.lang.UnsatisfiedLinkError
            if e.getMessage.equals(
              "com.microsoft.z3.Native.INTERNALgetErrorMsgEx(JI)Ljava/lang/String;"
            ) =>
          // weird unintuitive error z3 can have when an input type is incorrect in a way it doesn't check
          // REMEMBER: can be caused by incorrect types (e.g. gamma vars should be of type bool)
          throw error.Z3Error(
            "Z3 failed",
            cond,
            "incorrect z3 expression type, probably involving ForAll/Exists"
          )
        case e: Throwable =>
          // throw error.Z3Error("Z3 failed", cond, e)
          throw e
      } finally {
        solver.pop()
      }

    if (simplify && res == z3.Status.SATISFIABLE) println(solverSimplify(cond, false))
    // solverSimplify(cond).getSubgoals.map(g => println("val: " + translateBack(g.AsBoolExpr)))

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
  }

  // TODO put in proper types
  def formula(prop: Expression, expectIds: Boolean = false): z3.BoolExpr =
    translate(prop, expectIds) match {
      case b: z3.BoolExpr => b
      case e =>
        throw error.InvalidProgram("not a boolean expression", prop, e)
    }

  def arith(prop: Expression, expectIds: Boolean = false): z3.IntExpr =
    translate(prop, expectIds) match {
      case arith: z3.IntExpr => arith
      // treating bit vectors as unsigned
      case bitVec: z3.BitVecExpr => ctx.mkBV2Int(bitVec, false)
      case e =>
        throw error.InvalidProgram("not an arithmetic expression", prop, e)
    }

  def bitwise(prop: Expression, expectIds: Boolean = false): z3.BitVecExpr =
    translate(prop, expectIds) match {
      case bitVec: z3.BitVecExpr => bitVec
      case arith: z3.IntExpr     => ctx.mkInt2BV(intSize, arith)
      case e =>
        throw error.InvalidProgram("not a bitwise expression", prop, e)
    }

  def handleSelect(
      store: Expression,
      arr: z3.ArrayExpr,
      expectIds: Boolean
  ): z3.Expr = store match {
    case a: VarAccess => ctx.mkSelect(arr, translate(a.index, expectIds))
    case a: VarStore  => handleSelect(a.array, arr, expectIds)
    case _            => throw new Error("Unexpected statement in VarStore")
  }

  // TODO i think the name should come from the inner load not from the store
  def handleStore(
      store: Expression,
      expectIds: Boolean
  ): z3.ArrayExpr = store match {
    case a: VarAccess =>
      ctx.mkArrayConst(
        a.name.toString,
        ctx.getIntSort,
        if (a.ident.gamma) ctx.getBoolSort else ctx.getIntSort
      )
    case a: VarStore =>
      ctx.mkStore(
        handleStore(a.array, expectIds),
        translate(a.index, expectIds),
        // TODO  Type?
        translate(a.exp, expectIds)
      )
    case _ => throw new Error("Unexpected statement in VarStore")
  }

  /* currently doing all arithmetic operations on ints - may want to switch to bitvectors
   and bitwise arithmetic operations for better simulation of the assembly semantics if this ends up being important
  https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html */
  def translate(prop: Expression, expectIds: Boolean): z3.Expr = prop match {
    case Const._true  => ctx.mkTrue
    case Const._false => ctx.mkFalse

    case Lit(n: Int) => ctx.mkInt(n)

    // TODO: case Var(Id.indexId, _, _) => throw new Error("Unsubstituted index")
    case x: Var =>
      if (expectIds) throw new Error("Program ids should not be resolved")
      // TODO println(s"$x is of type ${typeOf}")
      val sort = if (x.ident.expType == TBool) ctx.getBoolSort else ctx.getIntSort
      ctx.mkConst(x.toString, sort)
    case x: Id =>
      if (expectIds) throw new Error("Unresolved id")
      val sort = if (x.expType == TBool) ctx.getBoolSort else ctx.getIntSort
      ctx.mkConst(x.toString, sort)

    // TODO can these cases be merged together
    case x: VarAccess =>
      if (expectIds) throw new Error("Program ids should not be resolved")
      // TODO this is incorrect
      // TODO
      val sort = if (x.name.ident.gamma) ctx.getBoolSort else ctx.getIntSort
      ctx.mkSelect(
        ctx.mkArrayConst(x.name.toString, ctx.getIntSort, sort),
        translate(x.index, expectIds)
      )
    case x: IdAccess =>
      if (!expectIds) throw new Error("unresolved array id")
      val sort = if (x.ident.gamma) ctx.getBoolSort else ctx.getIntSort
      ctx.mkSelect(
        ctx.mkArrayConst(x.ident.toString, ctx.getIntSort, sort),
        translate(x.index, expectIds)
      )

    case store: VarStore =>
      handleSelect(
        store,
        handleStore(
          store,
          expectIds
        ),
        expectIds
      )

    /*
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

    case BinOp("==", _, TBool, arg1, arg2) =>
      ctx.mkEq(translate(arg1, expectIds), translate(arg2, expectIds))
    case BinOp("!=", _, TBool, arg1, arg2) =>
      ctx.mkNot(
        ctx.mkEq(translate(arg1, expectIds), translate(arg2, expectIds))
      )

    case PreOp("!", TBool, TBool, arg) => ctx.mkNot(formula(arg, expectIds))
    case BinOp("&&", TBool, TBool, arg1, arg2) =>
      ctx.mkAnd(formula(arg1, expectIds), formula(arg2, expectIds))
    case BinOp("||", TBool, TBool, arg1, arg2) =>
      ctx.mkOr(formula(arg1, expectIds), formula(arg2, expectIds))

    case BinOp("=>", TBool, TBool, arg1, arg2) =>
      ctx.mkImplies(formula(arg1, expectIds), formula(arg2, expectIds))

    case PreOp("-", TInt, TInt, arg) => ctx.mkUnaryMinus(arith(arg))
    case BinOp("+", TInt, TInt, arg1, arg2) =>
      ctx.mkAdd(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("-", TInt, TInt, arg1, arg2) =>
      ctx.mkSub(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("*", TInt, TInt, arg1, arg2) =>
      ctx.mkMul(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("/", TInt, TInt, arg1, arg2) =>
      ctx.mkDiv(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("%", TInt, TInt, arg1, arg2) =>
      ctx.mkMod(arith(arg1, expectIds), arith(arg2, expectIds))

    case BinOp("<=", TInt, TBool, arg1, arg2) =>
      ctx.mkLe(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("<", TInt, TBool, arg1, arg2) =>
      ctx.mkLt(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp(">=", TInt, TBool, arg1, arg2) =>
      ctx.mkGe(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp(">", TInt, TBool, arg1, arg2) =>
      ctx.mkGt(arith(arg1, expectIds), arith(arg2, expectIds))

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
     */

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

    /*
    case Exists(bound, body) =>
      ctx.mkExists(bound.toArray map translate, translate(body), 0, scala.Array(), null, null, null)
     */

    case BinOp(_, t1, t2, _, _) =>
      throw new Error(s"cannot translate to SMT $prop of type $t1 $t2")

    case _ =>
      throw new Error(s"cannot translate to SMT $prop")
  }
}
