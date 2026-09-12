import Compilatrix.Tools.IxIR2Check

open Lean System Compilatrix.Tools.Check Compilatrix.Tools.IxIR2Check

private def boolean (value : Json) (key : String) : IO Bool := checked (value.getObjValAs? Bool key)

private def filename (value : Json) (key : String) : IO String := do
  let name ← strField value key
  need (!name.isEmpty && !name.startsWith "." && !name.contains ".." &&
    name.toList.all (fun c => c.isAlphanum || c == '-' || c == '.')) "invalid snapshot filename"
  return name

private def probe (exe stage : String) (path : FilePath) (root : String)
    (limits : Limits) (accepts : Bool) : IO Unit := do
  let result ← IO.Process.output { cmd := exe, args := #["--probe", stage, path.toString, root,
    toString limits.maxBytes, toString limits.maxNatBytes, toString limits.maxSequence, toString limits.maxBlobBytes] }
  if accepts then
    need (result.exitCode == 0 && result.stdout.contains s!"ixir2 probe ok: {stage}")
      s!"public {stage} ingress rejected {path.fileName}: {result.stderr}"
  else
    need (result.exitCode == 1 && result.stderr.contains "ixir2 fixture failed:")
      s!"public {stage} ingress did not reject normally: {path.fileName}\n{result.stdout}{result.stderr}"

private def limitsOf (row : Json) : IO Limits := do
  let value ← field row "limits"
  return {
    maxBytes := ← nat (← field value "maxBytes")
    maxNatBytes := ← nat (← field value "maxNatBytes")
    maxSequence := ← nat (← field value "maxSequence")
    maxBlobBytes := ← nat (← field value "maxBlobBytes") }

private def inspectBoundary (exe : String) (directory : FilePath) (row : Json) : IO Unit := do
  let name ← filename row "binary"
  let bytes ← IO.FS.readBinFile (directory / name)
  need (bytes.size == (← nat (← field row "bytes"))) "boundary byte count mismatch"
  need (root bytes == (← strField row "digest")) "boundary payload mismatch"
  let limits ← limitsOf row
  let stage ← strField row "stage"
  let accepts ← boolean row "accepts"
  let expectedRoot ← strField row "root"
  let decoded := decodeWith limits bytes
  match stage with
  | "syntax" => need (decoded.isOk == accepts) "independent bounded syntax result mismatch"
  | "address" => need ((decoded.isOk && root bytes == expectedRoot) == accepts) "independent root result mismatch"
  | "ingress" => need decoded.isOk "metadata rejection did not have canonical syntax"
  | _ => throw (IO.userError "unknown boundary stage")
  probe exe stage (directory / name) expectedRoot limits accepts

def main (args : List String) : IO UInt32 := cli "IxIR2 snapshot check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "fixtures/ixir2/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run exe #[output.toString]) ["ixir2 fixture ok:"] "IxIR2 snapshot producer"
    let report ← readJson (first / "report.json")
    inspectReport expected report
    let rows ← arrField report "cases"
    let boundaries ← arrField report "boundaries"
    let mut inventory := ["report.json"]
    for row in rows do
      inventory := (← filename row "binary") :: (← filename row "snapshot") :: inventory
    for row in boundaries do inventory := (← filename row "binary") :: inventory
    need (inventory.eraseDups.length == inventory.length) "duplicate snapshot filenames"
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      let files ← output.readDir
      need ((files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "snapshot artifact inventory mismatch"
      for file in files do need (!(← file.path.isDir)) "unexpected snapshot directory"
    for name in inventory do
      need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
        s!"fresh processes produced different IxIR2 artifacts: {name}"
    for output in [first, second] do
      for row in rows do
        let binary ← filename row "binary"
        let bytes ← IO.FS.readBinFile (output / binary)
        inspectCase row bytes (← readJson (output / (← filename row "snapshot")))
        probe exe (if ← boolean row "checked" then "ingress" else "address")
          (output / binary) (← strField row "root") {} true
      for row in boundaries do inspectBoundary exe output row
    let some hot := rows.find? (fun row => (row.getObjValAs? String "name").toOption == some "map-hot-reuse")
      | throw (IO.userError "missing allocating-call snapshot")
    let regressions ← regressionChecks hot (← IO.FS.readBinFile (first / (← filename hot "binary")))
      (← readJson (first / (← filename hot "snapshot"))) report
    IO.println s!"IxIR2 snapshot check ok: {rows.size} snapshots, {boundaries.size} boundaries, two fresh artifact sets, {regressions} independent corruption regressions"
