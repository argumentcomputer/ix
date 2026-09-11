import Ix.Compiler.Tools.UniqueCheck

/-! Fresh-process gate for checked source unique reversal artifacts. -/

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def main (args : List String) : IO UInt32 := cli "source unique reuse check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-unique-reuse/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      let result ← run exe #[output.toString]
      requireAll result ["source-unique-reuse ok:"] "unique producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed unique source, identity, counter, or rejection matrix drifted"
    let rows ← arrField report "cases"
    need (rows.size == 7 && (← arrField report "policy_and_rejection_checks").size == 43) "unique matrix inventory disagreement"
    let mut inventory := ["report.json"]
    for row in rows do
      let name ← strField row "snapshot"
      need (!name.isEmpty && !name.startsWith "." && !name.contains ".." &&
        name.toList.all (fun c => c.isAlphanum || c == '-' || c == '.') && !inventory.contains name) "invalid snapshot name"
      inventory := name :: inventory
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      let files ← output.readDir
      need ((files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "unique artifact inventory drifted"
      for file in files do need (!(← file.path.isDir)) "unexpected unique artifact directory"
    for name in inventory do
      need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name))) s!"fresh artifact disagreement: {name}"
    for row in rows do inspectSnapshot row (← readJson (first / (← strField row "snapshot")))
    let some three := rows.find? (fun row => (row.getObjValAs? String "name").toOption == some "three")
      | throw (IO.userError "missing three-element regression")
    regressionChecks three (← readJson (first / (← strField three "snapshot")))
    IO.println s!"source unique reuse check ok: {rows.size} Ixon reversals, two fresh artifact sets, canonical preimages, 12 corruption regressions, all prefixes and reclaimed heaps checked"
