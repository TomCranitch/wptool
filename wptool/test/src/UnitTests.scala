import org.scalatest.funsuite.AnyFunSuite
import wptool.{Assert, Assignment, Assume, Atomic, BinOp, Block, Const, High, Id, If, Lit, Passify, PassifyState, State, Var, VarDef, WPTool}

class UnitTests extends  AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/"

  /* Tests for Passify */
  test("Passify assignment") {
    val id = Id("x")
    val control = Var("c", 9, Const._true, Const._true)
    val L = BinOp("==", control, Lit(4))
    val vari = Var("x", 2, Const._false, L)
    val state = PassifyState(Map((id, vari)), State(Set(new VarDef(id.name, L)), false, None), Map((id, High)), Map((id, L)))
    val (passStmt, _state) = Passify.execute(Assignment(id, Lit(2)), state)

    assert(_state.idVarMap.get(id) contains id.toVar(3, Const._true, L))
    assert(passStmt == Atomic(List(
      Assert(BinOp("&&",
        // Global => (L(x) => Gamma(x))
        BinOp("=>", Const._true, BinOp("=>", L, Const._true)),
        Const._true
      )),
      Assume(BinOp("==", id.toVar(3, Const._true, L), Lit(2)))
    )))
  }

  test("Passify if") {
    val id = Id("x")
    val vari = Var("x", 2, Const._false, Const._false)
    val state = PassifyState(Map((id, vari)), State(Set(new VarDef(id.name, Const._false)), false, None), Map((id, High)), Map((id, Const._false)))
    val (passStmt, _state) = Passify.execute(If(
      BinOp("==", vari, Lit(5)),
      Block(List(Assignment(id, Lit(6)))),
      None
    ), state)

    passStmt match {
      case ifStmt: If =>
        assert(ifStmt.test == BinOp("==", vari, Lit(5)))
        assert(ifStmt.left.statements.length == 1)
        ifStmt.right match {
          case Some(v) =>
            assert(v.statements.length == 1)
            // TDDO check gamma/L
            // TODO need to remove && at some point, but need to decide on gamma calculations for
            assert(v.statements.head == Assume(BinOp("==", Var("x", 3, BinOp("&&", Const._false, Const._true), Const._false), Var("x", 2, Const._false, Const._false))))
          case None => assert(false, "Right branch should be non-empty")
        }
      case _ => assert(false, "Passified statement should be an if")
    }
  }

  /* Tests for Exec */

}
