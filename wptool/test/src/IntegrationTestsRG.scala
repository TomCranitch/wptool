import org.scalatest.funsuite.AnyFunSuite
import wptool.WPTool

class IntegrationTestsRG extends  AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/rg/"
  val testNegDir: String = System.getProperty("user.dir") + "/tests/rg/neg/"

  test("Test assignment") {
    assert(WPTool.run(testDir + "assign0", debug = false))
    assert(WPTool.run(testDir + "assign1", debug = false))
    assert(WPTool.run(testDir + "assign2", debug = false))
  }

  test("Test assignment fails") {
    assert(!WPTool.run(testNegDir + "assign1", debug = false))
    assert(!WPTool.run(testNegDir + "assign2", debug = false))
  }
}
