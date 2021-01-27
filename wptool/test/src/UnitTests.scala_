import org.scalatest.funsuite.AnyFunSuite
import wptool._

class UnitTests extends AnyFunSuite {
  def createState(ids: Set[Id]) = State(ids.map(id => VarDef(id, Const._true, LocalVar)), false, false, false, None, None, None)

  test("WP Assignment") {
    val id = Id("id", false, false, false)
    val assignment = Assignment(id, Lit(0))

    val state = createState(Set(id))

    assert(Exec.wp(Const._true, assignment, state) == Const._true)
    assert(Exec.wp(BinOp("||", Lit(12), id.toVar(state)), assignment, state) == BinOp("||", Lit(12), Lit(0)))
  }

  test("WP Array Assignment") {
    val id = Id("id", false, false, false)
    val assignment = ArrayAssignment(IdAccess(id, Lit(0)), Lit(1))

    val state = createState(Set(id))

    assert(Exec.wp(Const._true, assignment, state) == Const._true)
    assert(
      Exec.wp(BinOp("||", Lit(12), VarAccess(id.toVar(state), Lit(2))), assignment, state) ==
        BinOp("||", Lit(12), VarStore(VarAccess(id.toVar(state), Lit(2)), Lit(0), Lit(1)))
    )
  }

  test("Exec Array Assignment") {
    val id = Id("id", false, false, false)
    val assignment = ArrayAssignment(IdAccess(id, Lit(0)), Lit(1))

    val state = createState(Set(id))

    // TODO assert(Exec.exec(assignment, state, false).Qs == List(Const._true))
  }

  // TODO Exec.exec

  test("z3 Array Translation") {
    // TODO
  }

}
