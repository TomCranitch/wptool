import org.scalatest.funsuite.AnyFunSuite
import wptool.WPTool

class IntegrationTests extends  AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/base/"
  val testNegDir: String = System.getProperty("user.dir") + "/tests/base/neg/"

  test("Test assignment") {
    assert(WPTool.run(testDir + "assign1", debug = false))
    assert(WPTool.run(testDir + "assign2", debug = false))
    assert(WPTool.run(testDir + "assign3", debug = false))
  }

  test("Test assignment fails") {
    assert(!WPTool.run(testNegDir + "assign1", debug = false))
    assert(!WPTool.run(testNegDir + "assign2", debug = false))
    assert(!WPTool.run(testNegDir + "assign3", debug = false))
    assert(!WPTool.run(testNegDir + "assign4", debug = false))
  }

  test("Test if") {
    assert(WPTool.run(testDir + "if1", debug = false))
    assert(WPTool.run(testDir + "if2", debug = false))
  }

  test("Test if fails") {
    assert(!WPTool.run(testNegDir + "if1", debug = false))
    assert(!WPTool.run(testNegDir + "if2", debug = false))
    assert(!WPTool.run(testNegDir + "if3", debug = false))
  }

  test("Test while") {
    assert(WPTool.run(testDir + "while1", debug = false))
  }

  test("Test while fails") {
    assert(!WPTool.run(testNegDir + "while1", debug = false))
    assert(!WPTool.run(testNegDir + "while2", debug = false))
    assert(!WPTool.run(testNegDir + "while3", debug = false))
    assert(!WPTool.run(testNegDir + "while4", debug = false))
  }
}
