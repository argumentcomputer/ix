import Compilatrix.Tools.CallReuseCheck

/-! Independent fresh-process artifact, resource, and reservation gate. -/

open Lean System Compilatrix.Tools.Check Compilatrix.Tools.CallReuseCheck

def main (args : List String) : IO UInt32 := cli "source call reuse check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "fixtures/source-call-reuse/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      let result ← run exe #[output.toString]
      requireAll result ["source-call-reuse ok:"] "source map producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed source map, policy, address, counter, or rejection matrix drifted"
    let rows ← arrField report "cases"
    need (!rows.isEmpty) "source map matrix has no cases"
    need (!(← arrField report "policy_and_rejection_checks").isEmpty) "source map rejection matrix is empty"
    let mut inventory := ["report.json"]
    for row in rows do
      let name ← strField row "snapshot"
      need (!name.isEmpty && !name.startsWith "." && !name.contains ".." &&
        name.toList.all (fun c => c.isAlphanum || c == '-' || c == '.') && !inventory.contains name)
        "invalid or duplicate source map snapshot name"
      inventory := name :: inventory
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      let files ← output.readDir
      need ((files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "fresh map artifact inventory drifted"
      for file in files do need (!(← file.path.isDir)) "unexpected directory in map artifacts"
    for name in inventory do
      need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
        s!"fresh compiler processes produced different map artifacts: {name}"
    for row in rows do inspectSnapshot row (← readJson (first / (← strField row "snapshot")))
    let some hot := rows.find? (fun row => (row.getObjValAs? String "name").toOption == some "three-hot")
      | throw (IO.userError "missing hot map regression case")
    regressionChecks hot (← readJson (first / (← strField hot "snapshot")))
    IO.println s!"source call reuse check ok: {rows.size} Ixon maps, two fresh artifact sets, 7 corruption regressions, all prefixes and reclaimed heaps checked"
