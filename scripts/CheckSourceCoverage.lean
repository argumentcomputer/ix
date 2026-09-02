import Compilatrix.Tools.X86Check

/-! Compare complete artifacts from two fresh compiler processes, check the
reviewed stage/identity/counter matrix, and independently inspect native exits.
The checker imports no compiler code; the producer is a separate executable. -/

open Lean System Compilatrix.Tools.Check Compilatrix.Tools.X86Check

private def fileName (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun char => char.isAlphanum || char == '-' || char == '.')
    && !name.contains ".." && !name.startsWith "."

private def requiredFields (value : Json) (keys : List String) (label : String) : IO Unit := do
  for key in keys do
    let _ ← field value key
  need (value != Json.null) s!"missing {label}"

private def inspectSnapshot (directory : FilePath) (row : Json) : IO Unit := do
  let path ← strField row "snapshot"
  need (fileName path) s!"invalid snapshot path {path}"
  let snapshot ← readJson (directory / path)
  need ((← strField snapshot "format") == "compilatrix/source-case/1") "unknown source snapshot format"
  let input ← field snapshot "input"
  need ((← field input "root") == (← field row "root")) "snapshot/report source root disagreement"
  need ((← arrField input "constants").size == (← nat (← field row "source_constants")))
    "snapshot/report source constant count disagreement"
  let stage ← strField row "last_accepted_stage"
  let compiled ← field snapshot "compilation"
  if stage == "ixir2" || stage == "elf" then
    need ((← strField compiled "format") == "compilatrix/compiler-snapshot/1") "missing compiler snapshot"
    let ir0 ← field compiled "ixir0"
    requiredFields ir0 ["raw_declarations", "raw_main", "groups", "declarations", "main", "blocks", "address_map"] "IxIR0"
    let ir1 ← field compiled "ixir1"
    requiredFields ir1 ["raw_declarations", "raw_main", "artifacts", "declarations", "main", "address_map", "reserved"] "IxIR1"
    need ((← field ir1 "root") == (← field row "ir1_root")) "snapshot/report IxIR1 root disagreement"
    let hpt ← field compiled "hpt"
    requiredFields hpt ["producer_limits", "producer_stats", "candidate", "artifacts"] "HPT"
    let certificates ← arrField hpt "artifacts"
    let roots ← certificates.mapM (field · "root")
    need (roots == (← arrField row "hpt_roots") && !roots.isEmpty) "snapshot/report HPT identity disagreement"
    for certificate in certificates do
      requiredFields certificate ["program_root", "cache_key", "dependencies", "members", "bytes"] "HPT certificate"
    requiredFields (← field compiled "ixir2_diagnostic")
      ["program", "validation_stats", "parameter_worlds", "constructors", "recursor_origins"] "IxIR2"
  else
    need (compiled == Json.null) "negative source snapshot unexpectedly contains a compiler output"

private def compareFiles (first second : FilePath) (report : Json) : IO (Array Json) := do
  let rows ← arrField report "source_cases"
  let mut expected := ["report.json"]
  for row in rows do
    let snapshot ← strField row "snapshot"
    need (fileName snapshot && !expected.contains snapshot) s!"invalid/duplicate snapshot {snapshot}"
    expected := snapshot :: expected
    let object ← field row "object"
    if object != Json.null then
      let name ← string object
      need (fileName name && !expected.contains name) s!"invalid/duplicate object {name}"
      expected := name :: expected
  expected := expected.mergeSort (· ≤ ·)
  for directory in [first, second] do
    let entries ← directory.readDir
    let actual := entries.toList.map (·.fileName) |>.mergeSort (· ≤ ·)
    need (actual == expected) s!"compiler output file inventory drifted: {repr actual}"
    for entry in entries do need (!(← entry.path.isDir)) s!"unexpected output directory {entry.path}"
  for name in expected do
    need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name)))
      s!"fresh compiler processes produced different complete artifacts: {name}"
  return rows

def main (args : List String) : IO UInt32 := cli "source coverage check failed" do
  let args ← checked (parseArgs [
    "--fixture", "--contact", "--expected", "--readelf", "--objdump", "--cc", "--harness"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let contact := option args "--contact" "fixtures/ixon-std-contact"
  let expected ← readJson (option args "--expected" "fixtures/source-coverage/expected.json")
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  let native ← nativeArgs args
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    -- Each invocation constructs and compiles all source inputs from scratch.
    for output in [first, second] do
      let result ← run exe #[output.toString, contact]
      requireAll result ["source-coverage ok:"] "coverage producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed source coverage, identity, or counter matrix drifted"
    let rows ← compareFiles first second report
    let mut objectCount := 0
    for row in rows do
      inspectSnapshot first row
      let object ← field row "object"
      if object == Json.null then continue
      objectCount := objectCount + 1
      let path := first / (← string object)
      let elf ← inspectElf readelf path
      need (elf.contains "There are no relocations in this file.") "source scalar has unexpected relocations"
      let observation ← field row "observation"
      let number ← nat (← field observation "nat")
      let disassembly ← disassemble objdump path
      requireAll disassembly [s!"movabs rax,0x{hexNat number}"] "source scalar target"
      let bytes ← IO.FS.readBinFile path
      need (containsBytes bytes (← provenance (← strField row "ir1_root")))
        "source object lost its exact addressed IxIR1 provenance"
      if let some (cc, harness) := native then
        linkAndRun cc readelf harness path (directory / s!"{← strField row "name"}-native") number
    need (objectCount > 0) "source coverage has no native-capable exit"
    let suffix := if native.isSome then ", native results agree" else ""
    IO.println s!"source coverage check ok: {rows.size} Ixon cases, two fresh complete artifact sets, {objectCount} ELF objects{suffix}"
