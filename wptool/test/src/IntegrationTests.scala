import org.scalatest.funsuite.AnyFunSuite
import wptool.WPTool

class IntegrationTests extends  AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/"
  val testNegDir: String = System.getProperty("user.dir") + "/tests/neg/"

  test("Test assignment") {
    assert(WPTool.run(testDir + "assign1", debug = false))
    assert(WPTool.run(testDir + "assign2", debug = false))
    assert(!WPTool.run(testDir + "assign3", debug = false))
    assert(!WPTool.run(testDir + "assign4", debug = false))
  }

  test("Test assignment fails") {
    assert(!WPTool.run(testNegDir + "assign1", debug = false))
  }

  test("Test if") {
    assert(!WPTool.run(testDir + "if1", debug = false))
    assert(WPTool.run(testDir + "if2", debug = false))
    assert(!WPTool.run(testDir + "if3", debug = false))
    assert(!WPTool.run(testDir + "if4", debug = false))
    assert(WPTool.run(testDir + "if5", debug = false))
  }
}
