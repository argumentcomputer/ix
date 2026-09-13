import Compilatrix.Tools.Check

/-! Independent process and artifact gate for source preparation. Compiler
implementation is not imported; observed clocks have no acceptance threshold. -/

open Lean System Compilatrix.Tools.Check

private def matrixNames := ["baseline", "edited", "blob-edited", "mutual", "wide-32", "wide-600"]
private def profileFiles := ["source.bin", "certificates.bin", "artifact.json", "summary.json"]

private def checkFiles (directory : FilePath) (expected : List String) : IO Unit := do
  let actual := (← directory.readDir).toList.map (·.fileName)
  need (actual.mergeSort (· ≤ ·) == expected.mergeSort (· ≤ ·)) s!"source-evidence inventory differs: {directory}"

private def sameFile (first second : FilePath) : IO Unit := do
  need ((← IO.FS.readBinFile first) == (← IO.FS.readBinFile second)) s!"source-evidence bytes differ: {first.fileName}"

private def measurements (path : FilePath) (replay : Bool := false) : IO Unit := do
  let value ← readJson path
  let rows ← if replay then array value else arrField value "cases"
  if !replay then
    need ((← strField value "format") == "compilatrix/source-evidence-cost-observations/1") "source-evidence clock format differs"
  need (rows.size == 1 && (← nat (← field rows[0]! "width")) == 32) "source-evidence smoke width differs"
  let expected := if replay then ["decode_retained_store", "restore_source_units", "assembly_total"] else
    ["cold_build", "unchanged_build", "decode_retained_store", "restore_source_units", "aggregate_preflight",
      "cache_record_preflight", "prepare_units_fresh", "prepare_units_with_addresses", "canonical_address_checks",
      "usage_checks", "encode_inputs", "encode_interfaces", "lookup_checked_units", "check_units_fresh",
      "check_units_prepared", "produce_units_prepared", "unit_observations", "assembly_total"]
  let phases ← arrField rows[0]! "phases"
  need ((← phases.toList.mapM (strField · "phase")) == expected) "source-evidence phase inventory differs"
  for phase in phases do let _ ← nat (← field phase "elapsed_ns")

private def mutation (exe : String) (input output file : FilePath)
    (change : ByteArray → ByteArray) (reason : String) : IO Unit := do
  let original ← IO.FS.readBinFile file
  try
    IO.FS.writeBinFile file (change original)
    let result ← IO.Process.output { cmd := exe, args := #["replay", input.toString, output.toString] }
    need (result.exitCode == 1 && result.stderr.contains "source-evidence:" && result.stderr.contains reason)
      s!"source-evidence replay did not reject {file.fileName}: {result.stdout}{result.stderr}"
  finally IO.FS.writeBinFile file original

def main (args : List String) : IO UInt32 := cli "source evidence check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected", "--modular-expected"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "fixtures/source-evidence/expected.json")
  let modularExpected ← readJson (option args "--modular-expected" "fixtures/source-modular/expected.json")
  need ((← arrField (← field expected "preparation_regressions") "cases").size == 38)
    "source preparation regression inventory differs"
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run exe #["run", output.toString, "smoke"])
        ["source preparation checks ok: 38", "source-evidence ok: 1 widths"] "source-evidence producer"
      checkFiles output ["modular", "profiles", "report.json", "measurements.json"]
      checkFiles (output / "profiles") ["wide-32"]
      checkFiles (output / "profiles/wide-32") profileFiles
      need ((← readJson (output / "report.json")) == expected) "reviewed source-evidence report drifted"
      need ((← readJson (output / "modular/report.json")) == modularExpected) "existing modular artifacts drifted"
      measurements (output / "measurements.json")
    sameFile (first / "report.json") (second / "report.json")
    for file in profileFiles do
      sameFile (first / "profiles/wide-32" / file) (second / "profiles/wide-32" / file)
    for name in matrixNames do
      for file in profileFiles do sameFile (first / "modular" / name / file) (second / "modular" / name / file)
    let replay := directory / "replay"
    requireAll (← run exe #["replay", first.toString, replay.toString])
      ["source-evidence replay ok: 1 widths"] "source-evidence replay"
    checkFiles replay ["modular", "profiles", "replay.json", "measurements.json"]
    measurements (replay / "measurements.json") true
    for file in profileFiles do
      sameFile (first / "profiles/wide-32" / file) (replay / "profiles/wide-32" / file)
    for name in matrixNames do
      for file in ["artifact.json", "certificates.bin"] do
        sameFile (first / "modular" / name / file) (replay / "modular" / name / file)
    let profile := first / "profiles/wide-32"
    mutation exe first (directory / "bad-source") (profile / "source.bin") (·.push 0) "recipe differs"
    mutation exe first (directory / "bad-store") (profile / "certificates.bin") (·.push 0) "trailing bytes"
    mutation exe first (directory / "bad-artifact") (profile / "artifact.json") (·.push 0) "artifact.json differs"
    mutation exe first (directory / "bad-summary") (profile / "summary.json") (·.push 0) "summary.json differs"
    mutation exe first (directory / "bad-report") (first / "report.json") (fun bytes => bytes.set! 0 0xff) "not UTF-8"
    IO.println "source evidence check ok: 38 preparation cases, 5 file mutations, exact fresh artifacts and retained replay"
