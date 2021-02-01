package wptool

import com.microsoft.z3
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.enumerations.Z3_decl_kind
import scala.reflect.runtime.universe.{TypeTag, typeOf}

object SMT {
  val intSize = 32 // size of bitvectors used
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver = ctx.mkSolver()

  def solverSimplify(cond: Expression[TBool], fast: Boolean) = {
    val g = ctx.mkGoal(true, false, false)
    g.add(formula(cond))
    // ctx.mkTactic(if (fast) "simplify" else "ctx-solver-simplify").apply(g)
    ctx.mkTactic("simplify").apply(g)
    // ctx.mkTactic("solve-eqs").apply(g)
  }

  def prove(
      cond: Expression[TBool],
      given: List[Expression[TBool]],
      debug: Boolean,
      simplify: Boolean,
      expectIds: Boolean = false
  ) = {
    if (debug)
      println("smt checking !(" + cond + ") given " + given.PStr)
    solver.push()
    val res =
      try {
        for (p <- given) {
          solver.add(formula(p, expectIds))
        }
        // check that (NOT cond) AND P is unsatisfiable
        solver.add(formula(PreOp("!", cond), expectIds))

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
            given.PStr,
            "incorrect z3 expression type, probably involving ForAll/Exists"
          )
        case e: Throwable =>
          // throw error.Z3Error("Z3 failed", cond, given.PStr, e)
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
  def formula(prop: Expression[Type], expectIds: Boolean = false): z3.BoolExpr =
    translate(prop, expectIds) match {
      case b: z3.BoolExpr => b
      case e =>
        throw error.InvalidProgram("not a boolean expression", prop, e)
    }

  def arith(prop: Expression[Type], expectIds: Boolean = false): z3.IntExpr =
    translate(prop, expectIds) match {
      case arith: z3.IntExpr => arith
      // treating bit vectors as unsigned
      case bitVec: z3.BitVecExpr => ctx.mkBV2Int(bitVec, false)
      case e =>
        throw error.InvalidProgram("not an arithmetic expression", prop, e)
    }

  def bitwise(prop: Expression[TInt], expectIds: Boolean = false): z3.BitVecExpr =
    translate(prop, expectIds) match {
      case bitVec: z3.BitVecExpr => bitVec
      case arith: z3.IntExpr     => ctx.mkInt2BV(intSize, arith)
      case e =>
        throw error.InvalidProgram("not a bitwise expression", prop, e)
    }

  def parseVarName(name: String) = {
    val prime = name.contains("'")
    val gamma = name.startsWith("Gamma_")
    val n =
      name.filter(l => !sub.contains(l)).stripPrefix("Gamma_").stripSuffix("'")
    Id(n, prime, gamma, false) // NOTE: if we need to use this well need to detect nought as well
  }

  def getArray[T <: Type](store: Expression[T]): z3.ArrayExpr = store match {
    case a: VarAccess[T] =>
      ctx.mkArrayConst(
        a.name.toString,
        ctx.getIntSort,
        if (a.ident.gamma) ctx.getBoolSort else ctx.getIntSort
      )
    case a: VarStore[T] => getArray(a.array)
    case _              => throw new Error("Unexpected statement in VarStore")
  }

  // TODO i think the name should come from the inner load not from the store
  def handleStore[T <: Type](
      store: Expression[T],
      arr: z3.ArrayExpr,
      expectIds: Boolean
  ): z3.Expr = store match {
    case a: VarAccess[T] => ctx.mkSelect(arr, translate(a.index, expectIds))
    case a: VarStore[T] =>
      handleStore(
        a.array,
        ctx.mkStore(
          arr,
          translate(a.index, expectIds),
          // TODO  Type?
          translate[Type](a.exp, expectIds)
        ),
        expectIds
      )
    case _ => throw new Error("Unexpected statement in VarStore")
  }

  /* currently doing all arithmetic operations on ints - may want to switch to bitvectors
   and bitwise arithmetic operations for better simulation of the assembly semantics if this ends up being important
  https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html */
  def translate[T <: Type](prop: Expression[T], expectIds: Boolean)(implicit typeTag: TypeTag[T]): z3.Expr = prop match {
    case Const._true  => ctx.mkTrue
    case Const._false => ctx.mkFalse

    case Lit(n: Int) => ctx.mkInt(n)

    // TODO: case Var(Id.indexId, _, _) => throw new Error("Unsubstituted index")
    case x: Var[_] =>
      if (expectIds) throw new Error("Program ids should not be resolved")
      typeOf[T] match {
        case t if typeOf[TInt] =:= typeOf[T]  => ctx.mkConst(x.toString, ctx.getIntSort)
        case t if typeOf[TBool] =:= typeOf[T] => ctx.mkConst(x.toString, ctx.getBoolSort)
        case _ =>
          println(s"$x is of type ${typeOf[T]}")
          ctx.mkConst(x.toString, ctx.getIntSort)
      }
    case x: Id[_] =>
      if (expectIds) throw new Error("Unresolved id")
      typeOf[T] match {
        case t if typeOf[TInt] =:= typeOf[T]  => ctx.mkConst(x.toString, ctx.getIntSort)
        case t if typeOf[TBool] =:= typeOf[T] => ctx.mkConst(x.toString, ctx.getBoolSort)
        case _ =>
          println(s"$x is of type ${typeOf[T]}")
          ctx.mkConst(x.toString, ctx.getIntSort)
      }

    // TODO can these cases be merged together
    case x: VarAccess[_] =>
      if (expectIds) throw new Error("Program ids should not be resolved")
      // TODO this is incorrect
      val sort = if (x.name.ident.gamma) ctx.getBoolSort else ctx.getIntSort
      ctx.mkSelect(
        ctx.mkArrayConst(x.name.toString, ctx.getIntSort, sort),
        translate(x.index, expectIds)
      )
    case x: IdAccess[_] =>
      if (!expectIds) throw new Error("unresolved array id")
      val sort = if (x.ident.gamma) ctx.getBoolSort else ctx.getIntSort
      ctx.mkSelect(
        ctx.mkArrayConst(x.ident.toString, ctx.getIntSort, sort),
        translate(x.index, expectIds)
      )

    case store: VarStore[T] =>
      handleStore(
        store,
        getArray(store),
        expectIds
      )

    case const: ArrayConstDefault[T] =>
      // TODO i dont think this is correct (https://stackoverflow.com/questions/54863754/z3-set-default-value-of-array-to-zero)
      if (const.name.ident.gamma)
        ctx.mkEq(
          ctx
            .mkArrayConst(const.name.toString, ctx.getIntSort, ctx.getBoolSort),
          ctx.mkConstArray(ctx.getIntSort, translate(const.const, expectIds))
        )
      else throw new Error("ArrayConstDefault is only for gamma values")

    case BinOp("==", arg1, arg2) =>
      ctx.mkEq(translate(arg1, expectIds), translate(arg2, expectIds))
    case BinOp("!=", arg1, arg2) =>
      ctx.mkNot(
        ctx.mkEq(translate(arg1, expectIds), translate(arg2, expectIds))
      )

    case PreOp("!", arg) => ctx.mkNot(formula(arg, expectIds))
    case BinOp("&&", arg1, arg2) =>
      ctx.mkAnd(formula(arg1, expectIds), formula(arg2, expectIds))
    case BinOp("||", arg1, arg2) =>
      ctx.mkOr(formula(arg1, expectIds), formula(arg2, expectIds))

    case BinOp("=>", arg1, arg2) =>
      ctx.mkImplies(formula(arg1, expectIds), formula(arg2, expectIds))

    case BinOp("==", arg1, arg2) =>
      ctx.mkEq(translate(arg1, expectIds), translate(arg2, expectIds))
    case BinOp("!=", arg1, arg2) =>
      ctx.mkNot(
        ctx.mkEq(translate(arg1, expectIds), translate(arg2, expectIds))
      )

    case PreOp("-", arg) => ctx.mkUnaryMinus(arith(arg))
    case BinOp("+", arg1, arg2) =>
      ctx.mkAdd(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("-", arg1, arg2) =>
      ctx.mkSub(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("*", arg1, arg2) =>
      ctx.mkMul(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("/", arg1, arg2) =>
      ctx.mkDiv(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("%", arg1, arg2) =>
      ctx.mkMod(arith(arg1, expectIds), arith(arg2, expectIds))

    case BinOp("<=", arg1, arg2) =>
      ctx.mkLe(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp("<", arg1, arg2) =>
      ctx.mkLt(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp(">=", arg1, arg2) =>
      ctx.mkGe(arith(arg1, expectIds), arith(arg2, expectIds))
    case BinOp(">", arg1, arg2) =>
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

    case _ =>
      throw new Error(s"cannot translate to SMT $prop")
  }
}
