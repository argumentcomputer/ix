import Compilatrix.Tools.SpaceCheck

open Lean System Compilatrix.Tools.Check Compilatrix.Tools.SpaceCheck

def main (args : List String) : IO UInt32 := cli "source space check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "fixtures/source-space/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run exe #[output.toString]) ["source-space ok:"] "source space producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed source space matrix drifted"
    inspectArena report
    let rows ← arrField report "cases"
    need (rows.size == 9 && (← arrField report "boundary_checks").size == 6) "space case or rejection inventory drifted"
    let mut inventory := ["report.json"]
    for row in rows do
      let name ← strField row "snapshot"
      need (!name.isEmpty && !name.startsWith "." && !name.contains ".." &&
        name.toList.all (fun c => c.isAlphanum || c == '-' || c == '.') && !inventory.contains name)
        "invalid or duplicate space snapshot name"
      inventory := name :: inventory
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      let files ← output.readDir
      need ((files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "fresh space artifact inventory drifted"
      for file in files do need (!(← file.path.isDir)) "unexpected space artifact directory"
    for name in inventory do
      need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
        s!"fresh processes produced different space artifacts: {name}"
    for row in rows do inspectSnapshot row (← readJson (first / (← strField row "snapshot")))
    let some hot := rows.find? (fun row => (row.getObjValAs? String "name").toOption == some "three-hot")
      | throw (IO.userError "missing suspended-allocation regression case")
    regressions hot (← readJson (first / (← strField hot "snapshot"))) report
    let total := (← rows.mapM (fun row => do nat (← field row "prefixes"))).foldl (· + ·) 0
    IO.println s!"source space check ok: 9 Ixon maps, {total} prefixes, 6 boundaries, 65 native byte budgets, two fresh artifact sets, 13 corruption regressions"
