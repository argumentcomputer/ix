import Compilatrix.Tools.Check

/-! Independent process and inventory gate; no compiler implementation is
imported here. Timings are inspected for shape, never thresholded. -/

open Lean System Compilatrix.Tools.Check

private def matrixNames : List String :=
  ["baseline", "edited", "blob-edited", "mutual", "wide-32", "wide-600"]

private def profileFiles : List String :=
  ["source.bin", "certificates.bin", "artifact.json", "raw.json", "addressed.json", "summary.json"]

private def checkFiles (directory : FilePath) (expected : List String) : IO Unit := do
  let actual := (← directory.readDir).toList.map (·.fileName)
  need (actual.mergeSort (· ≤ ·) == expected.mergeSort (· ≤ ·)) s!"assembly inventory differs: {directory}"

private def sameFile (first second : FilePath) : IO Unit := do
  need ((← IO.FS.readBinFile first) == (← IO.FS.readBinFile second)) s!"assembly bytes differ: {first.fileName}"

private def measurements (path : FilePath) (replay : Bool := false) : IO Unit := do
  let value ← readJson path
  let rows ← if replay then array value else arrField value "cases"
  need (rows.size == 1) "assembly smoke measurement width inventory differs"
  need ((← nat (← field rows[0]! "width")) == 32) "assembly smoke measurement width differs"
  let expected := if replay then ["decode_retained_store", "check_retained_units", "assembly_total"] else
    ["build_source_units", "program_preflight", "source_context", "erasure_and_IxIR0_addressing",
      "imported_evidence", "close_members", "entry_certificate", "IxIR1_raw_lowering",
      "IxIR1_indexed_addressing", "IxIR1_reference_addressing", "prepare_audit_indexes",
      "indexed_semantic_audit", "indexed_exact_image_audit", "reference_semantic_audit",
      "reference_exact_source_audit", "assembly_total"]
  let phases ← arrField rows[0]! "phases"
  need ((← phases.toList.mapM (strField · "phase")) == expected) "assembly phase inventory differs"
  for phase in phases do let _ ← nat (← field phase "elapsed_ns")

private def mutation (exe : String) (input output : FilePath) (file : FilePath)
    (change : ByteArray → ByteArray) (reason : String) : IO Unit := do
  let original ← IO.FS.readBinFile file
  try
    IO.FS.writeBinFile file (change original)
    let result ← IO.Process.output { cmd := exe, args := #["replay", input.toString, output.toString] }
    need (result.exitCode == 1 && result.stderr.contains "assembly-scaling:" && result.stderr.contains reason)
      s!"assembly replay did not reject {file.fileName}: {result.stdout}{result.stderr}"
  finally IO.FS.writeBinFile file original

def main (args : List String) : IO UInt32 := cli "assembly scaling check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected", "--modular-expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "fixtures/assembly-scaling/expected.json")
  let modularExpected ← readJson (option args "--modular-expected" "fixtures/source-modular/expected.json")
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run exe #["run", output.toString, "smoke"])
        ["assembly-scaling ok: 1 widths"] "assembly scaling producer"
      checkFiles output ["modular", "profiles", "report.json", "measurements.json"]
      checkFiles (output / "profiles") ["wide-32"]
      checkFiles (output / "profiles/wide-32") profileFiles
      need ((← readJson (output / "report.json")) == expected) "reviewed assembly reference matrix drifted"
      need ((← readJson (output / "modular/report.json")) == modularExpected) "existing modular artifacts drifted"
      measurements (output / "measurements.json")
    let regression ← field expected "address_regressions"
    need ((← arrField regression "cases").size == 20 &&
      (← nat (← field regression "malformed_result_rejections")) == 11)
      "address regression inventory drifted"
    sameFile (first / "report.json") (second / "report.json")
    for file in profileFiles do
      sameFile (first / "profiles/wide-32" / file) (second / "profiles/wide-32" / file)
    sameFile (first / "modular/report.json") (second / "modular/report.json")
    for name in matrixNames do
      for file in ["source.bin", "certificates.bin", "artifact.json", "summary.json"] do
        sameFile (first / "modular" / name / file) (second / "modular" / name / file)
    let replay := directory / "replay"
    requireAll (← run exe #["replay", first.toString, replay.toString])
      ["assembly-scaling replay ok: 1 widths"] "assembly scaling replay"
    checkFiles replay ["modular", "profiles", "replay.json", "measurements.json"]
    measurements (replay / "measurements.json") true
    for file in profileFiles do
      sameFile (first / "profiles/wide-32" / file) (replay / "profiles/wide-32" / file)
    for name in matrixNames do
      for file in ["artifact.json", "certificates.bin"] do
        sameFile (first / "modular" / name / file) (replay / "modular" / name / file)
    let profile := first / "profiles/wide-32"
    mutation exe first (directory / "bad-source") (profile / "source.bin") (·.push 0) "source recipe differs"
    mutation exe first (directory / "bad-store") (profile / "certificates.bin") (·.push 0) "trailing bytes"
    mutation exe first (directory / "bad-raw") (profile / "raw.json") (·.push 0) "raw.json differs"
    mutation exe first (directory / "bad-addressed") (profile / "addressed.json") (·.push 0) "addressed.json differs"
    mutation exe first (directory / "bad-artifact") (profile / "artifact.json") (·.push 0) "artifact.json differs"
    IO.println "assembly scaling check ok: 20 address cases, 11 malformed results, 5 file mutations, exact fresh artifacts and retained replay"
