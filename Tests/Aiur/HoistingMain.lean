import Tests.Aiur.Hoisting
import Tests.Aiur.Cross
import Tests.Aiur.Cost
import Tests.Aiur.Aiur
import Tests.Aiur.Hashes
import Tests.Aiur.RBTreeMap
import Tests.MultiStark
import Ix.IxVM.Core

private def runExisting (label : String) (source : Except Aiur.Global Aiur.Source.Toplevel)
    (cases : List AiurTestCase) (groups : Array (String × Array String) := #[]) : IO UInt32 := do
  IO.println label
  match AiurTestEnv.build source groups with
  | .error e => IO.eprintln s!"{label} setup failed: {e}"; return 1
  | .ok env => LSpec.lspecEachIO cases fun tc => pure (env.runTestCase tc)

/-- A focused runner for the existing Aiur suites, without compiling unrelated
Ix kernel/catalog tests. This reuses their cases and pinned cost expectations. -/
private def regression : IO UInt32 := do
  let r1 ← LSpec.lspecIO (.ofList [
    ("aiur-cross", [AiurTests.Cross.tests]), ("aiur-cost", [AiurTests.Cost.tests])]) []
  let r2 ← runExisting "aiur-prove" (pure toplevel) aiurTestCases
  let r3 ← runExisting "aiur-grouped" (pure toplevel) groupedTestCases testGroups
  let r4 ← match AiurTestEnv.build (pure toplevel) testGroups with
    | .error e => IO.eprintln s!"grouping setup failed: {e}"; pure 1
    | .ok env =>
      LSpec.lspecIO (.ofList [("aiur-grouping", [groupingStructureChecks env.compiled])]) []
  let r5 ← runExisting "aiur-blake3" (do
    let t ← IxVM.core.merge IxVM.byteStream; t.merge IxVM.blake3) blake3TestCases
  let r6 ← runExisting "aiur-sha256" (do
    let t ← IxVM.core.merge IxVM.byteStream; t.merge IxVM.sha256) sha256TestCases
  let r7 ← runExisting "aiur-rbtree-map" (pure IxVM.rbTreeMap) rbTreeMapTestCases
  let r8 ← Tests.MultiStark.selfTestSuite
  let r9 ← Tests.MultiStark.endToEndSuite
  return if [r1, r2, r3, r4, r5, r6, r7, r8, r9].all (· == 0) then 0 else 1

def main (args : List String) : IO UInt32 := do
  unless args.all (fun arg => arg == "--prove" || arg == "--regression") do
    IO.eprintln "usage: AiurHoistingTests [--prove] [--regression]"
    return 1
  let result ← AiurTests.Hoisting.suite (args.contains "--prove")
  let other ← if args.contains "--regression" then regression else pure 0
  return if result == 0 && other == 0 then 0 else 1
