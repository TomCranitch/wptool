import org.scalatest.funsuite.AnyFunSuite
import wptool.WPTool

class IntegrationTestsRG extends  AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/rg/"
  val testNegDir: String = System.getProperty("user.dir") + "/tests/rg/neg/"

  test("Assignment") {
    assert(WPTool.run(testDir + "assign0", debug = false))
    assert(WPTool.run(testDir + "assign1", debug = false))
    assert(WPTool.run(testDir + "assign2", debug = false))
  }

  test("Assignment (Negative)") {
    assert(!WPTool.run(testNegDir + "assign1", debug = false))
    assert(!WPTool.run(testNegDir + "assign2", debug = false))
    assert(!WPTool.run(testNegDir + "assign3", debug = false))
    assert(!WPTool.run(testNegDir + "assign4", debug = false))
  }

  ignore("CAS") {
    assert(WPTool.run(testDir + "cas1", debug = false))
  }

  ignore("CAS (Negative)") {
  }

  test("If") {
    assert(WPTool.run(testDir + "if1", debug = false))
    assert(WPTool.run(testDir + "if2", debug = false))
    assert(WPTool.run(testDir + "if3", debug = false))
  }

  test("If (Negative)") {
    assert(!WPTool.run(testNegDir + "if1", debug = false))
  }

  test("While") {
    assert(WPTool.run(testDir + "while1", debug = false))
  }

  test("While (Negative)") {
    assert(!WPTool.run(testNegDir + "while1", debug = false))
  }

  ignore("Spin Read") {
    assert(WPTool.run(testDir + "spinread/sync_read", debug = false))
    assert(WPTool.run(testDir + "spinread/sync_write", debug = false))
  }

  ignore("Spin Read (Negative)") {
    assert(!WPTool.run(testNegDir + "sync_read1", debug = false))
    assert(!WPTool.run(testNegDir + "sync_write1", debug = false))
  }
}
