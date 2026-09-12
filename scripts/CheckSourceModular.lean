import Compilatrix.Tools.Check

/-! This process imports no compiler or modular certificate implementation.
It freezes the complete report, compares fresh artifact sets, then exercises
the public retained-evidence checker in a separate process. -/

open Lean System Compilatrix.Tools.Check

private def names : List String :=
  ["baseline", "edited", "blob-edited", "mutual", "wide-32", "wide-600"]

private def checkFiles (directory : FilePath) (expected : List String) : IO Unit := do
  let actual := (← directory.readDir).toList.map (·.fileName)
  need (actual.mergeSort (· ≤ ·) == expected.mergeSort (· ≤ ·))
    s!"modular artifact inventory differs: {directory}"

private def sameFile (first second : FilePath) : IO Unit := do
  need ((← IO.FS.readBinFile first) == (← IO.FS.readBinFile second))
    s!"fresh modular artifacts differ: {first.fileName}"

private def inspectMeasurements (path : FilePath) (replay : Bool := false) : IO Unit := do
  let json ← readJson path
  let rows ← if replay then array json else arrField json "cases"
  need (rows.size == names.length) "modular measurement case inventory differs"
  let expected := if replay then
    ["decode_retained_store", "check_retained_source_certificates", "assembly_and_IxIR1_lowering"]
    else ["source_certificates", "assembly_and_IxIR1_lowering", "unchanged_source_certificates",
      "unchanged_assembly_and_IxIR1_lowering", "decode_retained_store", "check_retained_source_certificates",
      "restored_assembly_and_IxIR1_lowering", "monolithic_compilation"]
  for index in [:rows.size] do
    let row := rows[index]!
    need ((← strField row "name") == names[index]!) "modular measurement order differs"
    let phases ← arrField row "phases"
    need ((← phases.toList.mapM (strField · "phase")) == expected) "modular measurement phase inventory differs"
    for phase in phases do let _ ← nat (← field phase "elapsed_ns")

private def rejectedMutation (exe : String) (input output : FilePath)
    (file : FilePath) (mutated : ByteArray) (reason : String) : IO Unit := do
  let original ← IO.FS.readBinFile file
  try
    IO.FS.writeBinFile file mutated
    let result ← IO.Process.output { cmd := exe, args := #["replay", input.toString, output.toString] }
    need (result.exitCode == 1 && result.stderr.contains "source-modular:" && result.stderr.contains reason)
      s!"modular replay did not reject {file.fileName}: {result.stdout}{result.stderr}"
  finally IO.FS.writeBinFile file original

def main (args : List String) : IO UInt32 := cli "modular source check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "fixtures/source-modular/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run exe #["run", output.toString]) ["source-modular ok:"] "modular source producer"
      checkFiles output ("report.json" :: "measurements.json" :: names)
      inspectMeasurements (output / "measurements.json")
      for name in names do
        checkFiles (output / name) ["source.bin", "certificates.bin", "artifact.json", "summary.json"]
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed modular source matrix drifted"
    let rows ← arrField report "cases"
    need ((← rows.toList.mapM (strField · "name")) == names) "modular source case inventory drifted"
    need ((← arrField report "rejections").size == 40) "modular source rejection inventory drifted"
    for row in rows do
      let name ← strField row "name"
      need ((← nat (← field row "source_constants")) ==
        (← nat (← field row "reachable_source_constants"))) "fixture contains unreachable source constants"
      if name == "wide-600" then
        need ((← nat (← field row "source_constants")) == 611 &&
          (← nat (← field row "units")) == 11 &&
          (← nat (← field report "monolithic_candidate_limit")) == 512)
          "large modular closure or unchanged monolithic boundary drifted"
      let actions ← arrField row "build"
      for observation in actions do
        let unit ← strField observation "name"
        let action ← strField observation "action"
        let edited := name == "edited" || name == "blob-edited"
        need (action == if edited && unit == "unaffected" then "reused" else "produced")
          "source dependency-edit reuse differs"
      for observation in ← arrField row "unchanged" do
        need ((← strField observation "action") == "reused") "unchanged unit evidence was rebuilt"
    sameFile (first / "report.json") (second / "report.json")
    for name in names do
      for file in ["source.bin", "certificates.bin", "artifact.json", "summary.json"] do
        sameFile (first / name / file) (second / name / file)
    let replay := directory / "replay"
    requireAll (← run exe #["replay", first.toString, replay.toString])
      ["source-modular replay ok: 6 independently checked cases"] "modular source checker"
    checkFiles replay ("replay.json" :: "measurements.json" :: names)
    inspectMeasurements (replay / "measurements.json") true
    for name in names do
      checkFiles (replay / name) ["artifact.json", "certificates.bin"]
      for file in ["artifact.json", "certificates.bin"] do sameFile (first / name / file) (replay / name / file)
    let store := first / "baseline" / "certificates.bin"
    let storeBytes ← IO.FS.readBinFile store
    let source := first / "baseline" / "source.bin"
    let artifact := first / "baseline" / "artifact.json"
    rejectedMutation exe first (directory / "trailing") store (storeBytes.push 0) "trailing bytes"
    rejectedMutation exe first (directory / "truncated") store
      (storeBytes.extract 0 (storeBytes.size - 1)) "EOF"
    rejectedMutation exe first (directory / "version") store (storeBytes.set! 0 0) "unexpected framing bytes"
    rejectedMutation exe first (directory / "stale") store
      (← IO.FS.readBinFile (first / "edited" / "certificates.bin")) "stale or incompatible"
    rejectedMutation exe first (directory / "source") source
      ((← IO.FS.readBinFile source).push 0) "retained source recipe differs"
    rejectedMutation exe first (directory / "artifact") artifact
      ((← IO.FS.readBinFile artifact).push 0) "replayed artifact differs"
    IO.println "modular source check ok: 6 cases, 40 certificate rejections, 6 file mutations, two fresh artifact sets, independent retained replay"
