package wptool

import com.microsoft.z3
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.enumerations.Z3_decl_kind

object SMT {
  val intSize = 32 // size of bitvectors used
  val cfg = new java.util.HashMap[String, String]()
  val ctx = new z3.Context(cfg)
  val solver = ctx.mkSolver()

  def simplify(cond: Expression) = {
    val g = ctx.mkGoal(true, false, false)
    g.add(formula(cond))
    ctx.mkTactic("ctx-simplify").apply(g)
  }

  def solverSimplify(cond: Expression) = {
    val g = ctx.mkGoal(true, false, false)
    g.add(formula(cond))
    ctx.mkTactic("ctx-solver-simplify").apply(g)
  }

  def prove(
      cond: Expression,
      given: List[Expression],
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
          throw error.Z3Error("Z3 failed", cond, given.PStr, e)
      } finally {
        solver.pop()
      }

    if (simplify && res == z3.Status.SATISFIABLE) println(solverSimplify(cond))
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
      println(solverSimplify(cond))
    }
    res == z3.Status.UNSATISFIABLE
  }

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

  def parseVarName(name: String) = {
    val prime = name.contains("'")
    val gamma = name.startsWith("Gamma_")
    val n =
      name.filter(l => !sub.contains(l)).stripPrefix("Gamma_").stripSuffix("'")
    Id(n, prime, gamma, false) // NOTE: if we need to use this well need to detect nought as well
  }

  // TODO AND/OR can have multiple args
  // TODO can other operations have multiple args
  def translateBack(exp: z3.Expr): Expression =
    exp.getFuncDecl.getDeclKind match {
      case Z3_decl_kind.Z3_OP_TRUE  => Const._true
      case Z3_decl_kind.Z3_OP_FALSE => Const._false
      case Z3_decl_kind.Z3_OP_LABEL =>
        parseVarName(exp.getFuncDecl.getName.toString)
      case Z3_decl_kind.Z3_OP_ANUM =>
        // TODO this is so dodge
        Lit(exp.toString.toInt)
      case Z3_decl_kind.Z3_OP_AND =>
        constructMutliOp("&&", exp.getArgs.map(a => translateBack(a)).toList)
      case Z3_decl_kind.Z3_OP_OR =>
        constructMutliOp("||", exp.getArgs.map(a => translateBack(a)).toList)
      case Z3_decl_kind.Z3_OP_EQ =>
        BinOp(
          "==",
          translateBack(exp.getArgs()(0)),
          translateBack(exp.getArgs()(1))
        )
      case Z3_decl_kind.Z3_OP_NOT => PreOp("!", translateBack(exp.getArgs()(0)))
      case _ =>
        throw new Error(
          s"Unexpected exp ${exp} of kind ${exp.getFuncDecl.getDeclKind}"
        )
    }

  def handleStore(
      store: Expression,
      arr: z3.ArrayExpr,
      expectIds: Boolean
  ): z3.Expr = store match {
    case a: VarAccess => ctx.mkSelect(arr, translate(a.index, expectIds))
    case a: VarStore =>
      handleStore(
        a.array,
        ctx.mkStore(
          arr,
          translate(a.index, expectIds),
          translate(a.exp, expectIds)
        ),
        expectIds
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

    case x: Var =>
      if (expectIds) throw new Error("Program ids should not be resolved")
      if (x.ident.gamma) ctx.mkConst(x.toString, ctx.getBoolSort)
      else ctx.mkConst(x.toString, ctx.getIntSort)
    case x: Id =>
      if (!expectIds) throw new Error("unresolved id")
      if (x.gamma) ctx.mkConst(x.toString, ctx.getBoolSort)
      else ctx.mkConst(x.toString, ctx.getIntSort)

    // TODO can these cases be merged together
    case x: VarAccess =>
      if (expectIds) throw new Error("Program ids should not be resolved")
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
      handleStore(
        store,
        ctx.mkArrayConst(
          store.name.toString,
          ctx.getIntSort,
          if (store.isBool) ctx.getBoolSort else ctx.getIntSort
        ),
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

    /*
    case Exists(bound, body) =>
      ctx.mkExists(bound.toArray map translate, translate(body), 0, scala.Array(), null, null, null)
     */

    // array index
    // case VarAccess(name, index) => ctx.mkSelect(ctx.mkArrayConst(name.toString, ctx.getIntSort, ctx.getIntSort), translate(index))

    case _ =>
      throw new Error(s"cannot translate to SMT $prop")
  }
}
