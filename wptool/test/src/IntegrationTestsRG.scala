import org.scalatest.funsuite.AnyFunSuite
import wptool.WPTool

class IntegrationTestsRG extends AnyFunSuite {
  val testDir: String = System.getProperty("user.dir") + "/tests/rg/"
  val testNegDir: String = System.getProperty("user.dir") + "/tests/rg/neg/"

  def runTestFile(file: String) =
    WPTool.run(file, debug = false, simplify = false, silent = true)

  test("Assignment") {
    assert(runTestFile(testDir + "assign0"))
    assert(runTestFile(testDir + "assign1"))
    assert(runTestFile(testDir + "assign2"))
    // TODO i blieve this should be false assert(runTestFile(testDir + "assign3"))
    assert(runTestFile(testDir + "assign4"))
    assert(runTestFile(testDir + "assign5"))
    assert(runTestFile(testDir + "assign6"))
    assert(runTestFile(testDir + "assign7"))
  }

  test("Assignment (Negative)") {
    assert(!runTestFile(testNegDir + "assign1"))
    assert(!runTestFile(testNegDir + "assign2"))
    assert(!runTestFile(testNegDir + "assign4"))
    assert(!runTestFile(testNegDir + "assign5"))
    assert(!runTestFile(testNegDir + "assign6"))
  }

  test("Array") {
    assert(runTestFile(testDir + "array0"))
    assert(runTestFile(testDir + "array0_"))
    assert(runTestFile(testDir + "array1"))
    assert(runTestFile(testDir + "array2"))
    assert(runTestFile(testDir + "array3"))
    assert(runTestFile(testDir + "array4"))
    assert(runTestFile(testDir + "array5"))
    assert(runTestFile(testDir + "array6"))
  }

  test("Array (Negative)") {
    assert(!runTestFile(testNegDir + "array1"))
    assert(!runTestFile(testNegDir + "array2"))
    assert(!runTestFile(testNegDir + "array3"))
    assert(!runTestFile(testNegDir + "array4"))
    assert(!runTestFile(testNegDir + "array5"))
    assert(!runTestFile(testNegDir + "array6"))
    assert(!runTestFile(testNegDir + "array7"))
    assert(!runTestFile(testNegDir + "array8"))
  }

  test("CAS") {
    assert(runTestFile(testDir + "cas1"))
    assert(runTestFile(testDir + "cas2"))
  }

  ignore("CAS (Negative)") {}

  test("If") {
    assert(runTestFile(testDir + "if1"))
    assert(runTestFile(testDir + "if2"))
    assert(runTestFile(testDir + "if3"))
  }

  test("If (Negative)") {
    assert(!runTestFile(testNegDir + "if1"))
    assert(!runTestFile(testNegDir + "if2"))
    assert(!runTestFile(testNegDir + "if6"))
    assert(!runTestFile(testNegDir + "if7"))
    assert(!runTestFile(testNegDir + "if8"))
    assert(!runTestFile(testNegDir + "if9"))
  }

  test("While") {
    assert(runTestFile(testDir + "while1"))
    assert(runTestFile(testDir + "while2"))
    assert(runTestFile(testDir + "while3"))
    assert(runTestFile(testDir + "while4"))
  }

  test("While (Negative)") {
    assert(!runTestFile(testNegDir + "while1"))
    assert(!runTestFile(testNegDir + "while2"))
    assert(!runTestFile(testNegDir + "while3"))
    assert(!runTestFile(testNegDir + "while4"))
    assert(!runTestFile(testNegDir + "while5"))
  }

  test("SpinLock") {
    assert(runTestFile(testDir + "spinread/sync_read"))
    assert(runTestFile(testDir + "spinread/sync_write"))
  }

  test("SpinLock (Negative)") {
    assert(!runTestFile(testNegDir + "sync_read1"))
    assert(!runTestFile(testNegDir + "sync_write1"))
    assert(!runTestFile(testNegDir + "sync_write2"))
  }

  test("SeqLock") {
    assert(runTestFile(testDir + "seqlock/read"))
    assert(runTestFile(testDir + "seqlock/sync_write"))
  }

  test("SeqLock (Negative)") {
    assert(!runTestFile(testNegDir + "seqlock_read_1"))
    assert(!runTestFile(testNegDir + "seqlock_read_2"))
  }

  test("CasLev") {
    assert(runTestFile(testDir + "caslev/put"))
    assert(runTestFile(testDir + "caslev/steal"))
    assert(runTestFile(testDir + "caslev/take"))

  }

  test("CasLev (Negative)") {
    assert(!runTestFile(testNegDir + "caslev_steal1"))
    assert(!runTestFile(testNegDir + "caslev_steal2"))
    assert(!runTestFile(testNegDir + "caslev_steal3"))
    assert(!runTestFile(testNegDir + "caslev_steal4"))
    assert(!runTestFile(testNegDir + "caslev_put1"))
    assert(!runTestFile(testNegDir + "caslev_put2"))
    assert(!runTestFile(testNegDir + "caslev_put3"))
  }
}
