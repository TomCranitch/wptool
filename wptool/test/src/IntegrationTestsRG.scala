import org.scalatest.funsuite.AnyFunSuite
import wptool.WPTool

class IntegrationTestsRG extends  AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/rg/"
  val testNegDir: String = System.getProperty("user.dir") + "/tests/rg/neg/"

  test("Assignment") {
    assert(WPTool.run(testDir + "assign0", debug = false, silent = true))
    assert(WPTool.run(testDir + "assign1", debug = false, silent = true))
    assert(WPTool.run(testDir + "assign2", debug = false, silent = true))
    // TODO i blieve this should be false assert(WPTool.run(testDir + "assign3", debug = false, silent = true))
    assert(WPTool.run(testDir + "assign4", debug = false, silent = true))
    assert(WPTool.run(testDir + "assign5", debug = false, silent = true))
    assert(WPTool.run(testDir + "assign6", debug = false, silent = true))
  }

  test("Assignment (Negative)") {
    assert(!WPTool.run(testNegDir + "assign1", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "assign2", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "assign3", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "assign4", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "assign5", debug = false, silent = true))
  }

  test("CAS") {
    assert(WPTool.run(testDir + "cas1", debug = false, silent = true))
    assert(WPTool.run(testDir + "cas2", debug = false, silent = true))
  }

  ignore("CAS (Negative)") {
  }

  test("If") {
    assert(WPTool.run(testDir + "if1", debug = false, silent = true))
    assert(WPTool.run(testDir + "if2", debug = false, silent = true))
    assert(WPTool.run(testDir + "if3", debug = false, silent = true))
  }

  test("If (Negative)") {
    assert(!WPTool.run(testNegDir + "if1", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "if2", debug = false, silent = true))
  }

  test("While") {
    assert(WPTool.run(testDir + "while1", debug = false, silent = true))
    assert(WPTool.run(testDir + "while2", debug = false, silent = true))
    assert(WPTool.run(testDir + "while3", debug = false, silent = true))
    assert(WPTool.run(testDir + "while4", debug = false, silent = true))
  }

  test("While (Negative)") {
    assert(!WPTool.run(testNegDir + "while1", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "while2", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "while3", debug = false, silent = true))
  }

  test("Spin Read") {
    assert(WPTool.run(testDir + "spinread/sync_read", debug = false, silent = true))
    assert(WPTool.run(testDir + "spinread/sync_write", debug = false, silent = true))
  }

  test("Spin Read (Negative)") {
    assert(!WPTool.run(testNegDir + "sync_read1", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "sync_write1", debug = false, silent = true))
    assert(!WPTool.run(testNegDir + "sync_write2", debug = false, silent = true))
  }

  test("SeqLock") {
    assert(WPTool.run(testDir + "seqlock/read", debug = false, silent = true))
    assert(WPTool.run(testDir + "seqlock/sync_write", debug = false, silent = true))
  }
}
