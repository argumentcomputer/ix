import Ix.Compiler.Tools.X86Check
import Ix.Compiler.Tools.UpstreamNativeCheck

/-! Compare complete artifacts from two fresh compiler processes, check the
reviewed stage/identity/counter matrix, and independently inspect native exits.
The checker imports no compiler code; the producer is a separate executable. -/

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.X86Check

private def fileName (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun char => char.isAlphanum || char == '-' || char == '.')
    && !name.contains ".." && !name.startsWith "."

private def requiredFields (value : Json) (keys : List String) (label : String) : IO Unit := do
  for key in keys do
    let _ ← field value key
  need (value != Json.null) s!"missing {label}"

private def inspectUpstream (row input compiled observations : Json) : IO Unit := do
  requiredFields input ["manifest_bytes", "piece_bytes", "blob_inputs", "policy", "provenance"] "original upstream input"
  need ((← field input "provenance") == (← field row "provenance")) "upstream provenance disagreement"
  let provenance ← field row "provenance"
  need ((← strField provenance "source_pin") == "git:ix@6f18ea907b78d06f7dc0917c43beb385561c35f4" &&
      (← strField provenance "toolchain") == "leanprover/lean4:v4.33.1") "upstream writer pin drifted"
  requiredFields provenance ["source_module", "source_module_hash", "piece_hash", "members_root", "content_root"] "upstream provenance"
  if compiled == Json.null || (← strField row "last_accepted_stage") == "addressed-ixir0" then return
  need ((← field (← field compiled "source") "constants") == (← field input "constants"))
    "compiled upstream constants differ from their original byte records"
  let summary ← field row "observation"
  let number ← field summary "nat"
  for stage in ["ixon", "raw_ixir0", "ixir0"] do
    need ((← field observations stage) == number) s!"{stage} upstream result disagreement"
  for stage in ["raw_ixir1", "ixir1", "logical_ixir2", "physical_ixir2"] do
    let observation ← field observations stage
    need ((← field observation "nat") == number) s!"{stage} upstream result disagreement"
    requiredFields observation ["value", "store", "reclaimed"] "upstream heap observation"
    let store ← field observation "store"
    let reclaimed ← field observation "reclaimed"
    let (store, reclaimed) ← if stage.endsWith "ixir2" then
        pure (← field store "heap", ← field reclaimed "heap")
      else pure (store, reclaimed)
    let nodes ← arrField store "nodes"
    let live := nodes.countP (· != Json.null)
    need ((← nat (← field store "allocs")) == (← nat (← field store "frees")) + live)
      s!"{stage} upstream live-node balance disagrees"
    for key in ["allocs", "frees", "rcops", "reuses"] do
      need ((← field store key) == (← field (← field summary "heap") key)) s!"{stage} terminal counters disagree"
      need ((← field reclaimed key) == (← field (← field summary "reclaimed") key)) s!"{stage} reclaimed counters disagree"
    need ((← arrField reclaimed "nodes").all (· == Json.null) &&
        (← field reclaimed "allocs") == (← field reclaimed "frees")) s!"{stage} upstream result leaked"
  need ((← field observations "logical_ixir2") == (← field observations "physical_ixir2"))
    "complete upstream baseline stores or execution budgets disagree"

private def inspectAddressed (row compiled : Json) : IO Unit := do
  need ((← strField compiled "format") == "compilatrix/addressed-erasure/1" &&
      (← field compiled "source_erasure_certified") == toJson false)
    "partial addressed output was mislabeled as certified source erasure"
  need ((← strField (← field row "rejection") "stage") == "validated-erasure")
    "addressed source has an inconsistent next boundary"
  let ir0 ← field compiled "ixir0"
  requiredFields ir0 ["raw_declarations", "raw_main", "groups", "declarations", "main", "blocks", "address_map"] "addressed IxIR0"
  let groups ← arrField ir0 "groups"
  let blocks ← arrField ir0 "blocks"
  let mapping ← arrField ir0 "address_map"
  let mut raw := #[]
  let mut blockMaps := #[]
  let mut seen := #[]
  let mut index := 0
  for group in groups do
    let entries ← arrField group "entries"
    raw := raw ++ entries
    if (← strField group "kind") != "mutual" then continue
    let some block := blocks[index]? | throw (IO.userError "mutual producer block missing")
    index := index + 1
    let pairs ← arrField block "address_map"
    let members ← arrField block "members"
    need (pairs.size == entries.size && members.size == entries.size)
      "mutual producer/member map lost a row"
    for i in [:pairs.size] do
      let pair ← array pairs[i]!
      need (pair.size == 2 && pair[0]? == some (← field entries[i]! "key") &&
          pair[1]? == some (← field members[i]! "key")) "mutual producer map has wrong order or identity"
      need (!seen.contains pair[0]!) "mutual producer key was duplicated"
      seen := seen.push pair[0]!
    blockMaps := blockMaps ++ pairs
  need (index == blocks.size && blockMaps == mapping && raw == (← arrField ir0 "raw_declarations"))
    "addressed output omitted or reordered producers"
  let declarations ← arrField ir0 "declarations"
  need (declarations.size == raw.size) "addressed output dropped duplicate declaration rows"
  for left in declarations do
    for right in declarations do
      if (← field left "key") == (← field right "key") then
        need (left == right) "shared member identity has conflicting declarations"
  let name ← strField row "name"
  if name == "upstream-addClosed" || name == "std-failure-closure" then
    need (blocks.size == 3 && mapping.size == 3) "repeated-erasure upstream fixture lost a producer"
    for block in blocks do
      for key in ["root", "preimage", "members"] do
        need ((← field block key) == (← field blocks[0]! key)) "reused block artifact is not byte-exact"

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
  else if stage == "addressed-ixir0" then
    inspectAddressed row compiled
  else
    need (compiled == Json.null) "negative source snapshot unexpectedly contains a compiler output"
  if (← strField row "origin") == "upstream-lean" then
    inspectUpstream row input compiled (← field snapshot "observations")

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
    "--fixture", "--contact", "--upstream", "--expected", "--readelf", "--objdump", "--cc", "--harness"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let contact := option args "--contact" "Tests/Fixtures/Compiler/ixon-std-contact"
  let upstream := option args "--upstream" "Tests/Fixtures/Compiler/ixon-upstream"
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-coverage/expected.json")
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  let native ← nativeArgs args
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    -- Each invocation constructs and compiles all source inputs from scratch.
    for output in [first, second] do
      let result ← run exe #[output.toString, contact, upstream]
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
      let bytes ← IO.FS.readBinFile path
      if (← strField row "origin") == "upstream-lean" then
        let snapshot ← readJson (first / (← strField row "snapshot"))
        Ix.Compiler.Tools.UpstreamNativeCheck.inspect row snapshot bytes
        Ix.Compiler.Tools.UpstreamNativeCheck.regressions row snapshot bytes
        requireAll disassembly ["call", "add    rax,0x1"] "upstream computational target"
      else
        requireAll disassembly [s!"movabs rax,0x{hexNat number}"] "source scalar target"
        need (containsBytes bytes (← provenance (← strField row "ir1_root")))
          "source object lost its exact addressed IxIR1 provenance"
      if let some (cc, harness) := native then
        linkAndRun cc readelf harness path (directory / s!"{← strField row "name"}-native") number
    need (objectCount > 0) "source coverage has no native-capable exit"
    let suffix := if native.isSome then ", native results agree" else ""
    IO.println s!"source coverage check ok: {rows.size} Ixon cases, two fresh complete artifact sets, {objectCount} ELF objects{suffix}"
