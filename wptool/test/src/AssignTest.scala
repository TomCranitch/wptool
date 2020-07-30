import org.scalatest.funsuite.AnyFunSuite
import wptool.WPTool

class AssignTest extends  AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/"


  // TODO fails - noclassdeffounderror
  test("Test assign1") {
    println(testDir)
    assert(WPTool.run(testDir + "assign1", debug = false))
  }
}
