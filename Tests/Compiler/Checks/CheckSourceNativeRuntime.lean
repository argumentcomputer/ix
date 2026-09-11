import Ix.Compiler.Tools.UniqueCheck
import Ix.Compiler.Tools.X86Check

/-! Independent runtime-function artifact gate. No compiler, selector,
encoder, writer, or evaluator is imported. One object pair is linked once;
the resulting process supplies every runtime argument and observes release. -/

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck Ix.Compiler.Tools.X86Check

private def fileName (name : String) : Bool :=
  !name.isEmpty && !name.startsWith "." && !name.contains ".." &&
    name.toList.all (fun char => char.isAlphanum || char == '-' || char == '.')

private def rejectionNames (count : Nat) : List String :=
  ["length-sixty-five", "length-word-max", "null-descriptor", "misaligned-descriptor", "wrong-cursor",
   "insufficient-capacity", "zero-capacity", "excess-capacity", "misaligned-capacity", "wrong-allocs", "wrong-frees",
   "wrong-reuses", "wrong-live", "wrong-peak", "wrong-rcops", "wrong-payload", "wrong-reservations",
   "nil-tag", "nil-head", "nil-tail", "nil-padding"] ++
  (if count == 0 then [] else ["cons-tag", "cons-self-tail", "cons-null-tail", "cons-outside-tail", "cons-padding"])

private def inspectHeap (heap : Json) (input : Array Json) (phase : String) : IO Unit := do
  let count := input.size
  let initial := phase == "input"
  let reclaimed := phase == "reclaimed"
  let header ← (← arrField heap "header").mapM nat
  need (header.size == 10) "runtime header shape disagreement"
  need (header[7]! == 0 && header[9]! == 0) "runtime RC or reservation disagreement"
  let expected : Array Nat := if initial then
      #[32 * (count + 1), 32 * (count + 2), count + 1, 0, 0, count + 1, count + 1, 0, 0, 0]
    else #[32 * (count + 2), 32 * (count + 2), count + 2, if reclaimed then count + 2 else 1,
      count, if reclaimed then 0 else count + 1, count + 2, 0, 2 * count, 0]
  need (header == expected) "runtime allocation or reclamation disagreement"
  let cells ← arrField heap "cells"
  need (cells.size == count + 2) "runtime cell inventory disagreement"
  for index in [:cells.size] do
    let fields ← array cells[index]!
    need (fields.size == 4 && (← nat fields[3]!) == 0) "runtime padding disagreement"
    if reclaimed || (!initial && index == 0) then
      need (fields == #[toJson (3 : Nat), toJson (0 : Nat), Json.null, toJson (0 : Nat)]) "runtime cell not fully reclaimed"
    else if index == count + 1 || (initial && index == 0) then
      need (fields == #[toJson (0 : Nat), toJson (0 : Nat), Json.null, toJson (0 : Nat)]) "runtime nil or spare cell disagreement"
    else
      need ((← nat fields[0]!) == 1 && fields[1]! == input[count - index]!) "runtime payload disagreement"
      need (fields[2]! == toJson (if initial then index - 1 else index + 1)) "runtime pointer disagreement"

private def inspectPrefixes (observations : Json) (count : Nat) (foldCounters : Bool) : IO Unit := do
  let prefixes ← arrField observations "prefixes"
  need (prefixes.size == (if foldCounters then 7 else 8) * count + 22) "runtime macro-boundary inventory disagreement"
  let mut previous := 0
  for index in [:prefixes.size] do
    let row := prefixes[index]!
    let step ← number row "step"
    need ((index == 0 && step == 0) || (index > 0 && previous < step)) "runtime prefix sequence gap"
    previous := step
    let block ← number row "block"
    let offset ← number row "offset"
    let halted := (← field row "halted") == toJson true
    need (offset == 0 || (block == 2 && offset == 20) || (!foldCounters && block == 5 && offset == 10) || halted)
      "runtime observation is not a macro boundary"
    let header ← (← arrField row "header").mapM nat
    let tags ← (← arrField row "tags").mapM nat
    need (header.size == 10 && tags.all (· < 4)) "runtime prefix memory shape disagreement"
    let live := tags.countP (fun tag => tag == 0 || tag == 1)
    let reservations := tags.countP (· == 2)
    let freed := tags.countP (· == 3)
    need (header[0]! == 32 * tags.size && header[1]! == 32 * (count + 2) &&
      header[2]! == tags.size && header[3]! == freed && header[5]! == live && header[9]! == reservations &&
      reservations ≤ 1 && count + 1 ≤ tags.size && tags.size ≤ count + 2) "runtime prefix ownership accounting disagreement"
    need (header[7]! == 0 && live ≤ header[6]! && header[6]! ≤ count + 2) "runtime prefix RC or peak disagreement"
    need (halted == (index + 1 == prefixes.size)) "runtime prefix halt disagreement"
  need (previous == (if foldCounters then 30 else 42) * count + 82) "runtime control cost disagreement"
  need ((← field prefixes.back! "header") == (← field (← field observations "returned") "header"))
    "runtime terminal prefix disagrees"

private def inspectPipeline (report pipeline : Json) (foldCounters : Bool) : IO Unit := do
  need ((← strField pipeline "format") == "compilatrix/source-native-runtime-pipeline/1") "runtime pipeline format disagreement"
  let source ← field pipeline "source"
  need ((← field source "identity") == (← field report "source_identity") &&
    (← field source "argument_worlds") == toJson ["unique"] && (← strField source "result_world") == "unique" &&
    (← field source "entry_refs") == Json.arr #[← field source "root"]) "runtime source function contract disagreement"
  let constants ← arrField source "constants"
  need (constants.size == 8) "runtime source inventory disagreement"
  let constantBytes ← constants.mapM fun entry => do
    hashField entry "bytes" "key" "Ixon constant"
    return (← byteField entry "key") ++ blob (← byteField entry "bytes")
  let refs ← (← arrField source "entry_refs").mapM bytes
  let univs ← (← arrField source "entry_univs").mapM fun value => do return blob (← bytes value)
  let sourceBytes := "compilatrix/closed-ixon-input/1\x00".toUTF8 ++ vector constantBytes ++ vector refs ++ vector univs ++
    blob (← byteField source "entry")
  need (sourceBytes == (← byteField source "input_bytes")) "runtime source canonical preimage disagreement"
  hashField source "input_bytes" "identity" "source"
  let ir0 ← field pipeline "ixir0"
  for name in ["raw", "raw_main", "declarations", "main", "groups", "blocks", "address_map"] do
    need ((← field ir0 name) != Json.null) s!"missing runtime IxIR0 artifact: {name}"
  let graph ← field pipeline "ixir1"
  need ((← field graph "root") == (← field report "ixir1_root")) "runtime graph identity disagreement"
  let artifacts ← arrField graph "artifacts"
  need (artifacts.size == 2 && (← field artifacts[0]! "root") == (← field pipeline "entry_address") &&
    (← field artifacts[1]! "root") == (← field pipeline "worker_address") &&
    (← field pipeline "entry_address") != (← field pipeline "worker_address")) "runtime function inventory disagreement"
  let artifactBytes ← artifacts.mapM fun artifact => do
    need ((← strField artifact "kind") == "ordinary") "runtime function is not canonically addressed"
    hashField artifact "preimage" "root" "IxIR1 declaration"
    return tag 1 ++ (← byteField artifact "root") ++ blob (← byteField artifact "preimage")
  let graphBytes := "compilatrix/ixir1/optimizer-graph/1\x00".toUTF8 ++ vector artifactBytes ++ blob (← byteField graph "main")
  need (digest graphBytes == (← strField graph "root")) "runtime graph preimage disagreement"
  let abi ← field pipeline "abi"
  let selector := if foldCounters then "unique-reverse-runtime-x86/2" else "unique-reverse-runtime-x86/1"
  need ((← strField abi "policy") == "unique-list-runtime-arena/1" &&
    (← strField abi "selector") == selector &&
    (← number abi "max_length") == 64 && (← number abi "header_words") == 10 && (← number abi "cell_words") == 4)
    "runtime ABI disagreement"
  let policies ← field pipeline "policies"
  let policyValues := [("source", "unique-reverse-runtime/1"), ("usage", "recursor-modes/1"),
    ("lowering", "consuming-unique-recursor/1"), ("reuse", "static-unique-reuse/1"), ("execution", "call-local/0")]
  for (key, expected) in policyValues do
    need ((← strField policies key) == expected) "runtime policy disagreement"
  let target ← field pipeline "ixir2_diagnostic"
  for key in ["baseline", "selected", "baseline_stats", "selected_stats"] do
    need ((← field target key) != Json.null) s!"missing runtime target artifact: {key}"
  let limits ← field target "limits"
  let limitValues ← ["maxDeclarations", "maxBlocks", "maxBlocksPerFunction", "maxInstructionsPerBlock", "maxValueParams",
    "maxCreditParams", "maxOperands", "maxAlternatives", "maxValueRegisters", "maxCreditRegisters", "maxScalarLeafFacts",
    "maxFlowWork"].toArray.mapM fun key => do return uleb (← number limits key)
  let schema ← field pipeline "schema"
  for role in ["main", "release"] do
    let object ← field pipeline role
    let version := if role == "main" then (if foldCounters then 3 else 1) else 2
    need ((← strField object "file") == s!"{role}.o" && (← strField object "role") == role &&
      (← strField object "symbol") == (if role == "main" then "compilatrix_runtime_reverse" else "compilatrix_runtime_drop"))
      "runtime object role disagreement"
    need ((← number object "lowering_version") == 3 && (← number object "role_version") == version)
      "runtime object version disagreement"
    let expected := "compilatrix/native-runtime-unique-provenance/1\x00".toUTF8 ++
      (← byteField source "identity") ++ (← byteField graph "root") ++
      (← byteField pipeline "entry_address") ++ (← byteField pipeline "worker_address") ++
      (policyValues.foldl (fun out pair => out ++ blob pair.2.toUTF8) ByteArray.empty) ++
      uleb (← number policies "check_fuel") ++ uleb (← number policies "erase_fuel") ++ vector limitValues ++
      blob "unique-list-runtime-arena/1".toUTF8 ++ blob selector.toUTF8 ++ uleb 64 ++ uleb 10 ++ uleb 4 ++
      (← byteField schema "nil") ++ (← byteField schema "cons") ++ blob role.toUTF8 ++ uleb 3 ++ uleb version ++
      (if foldCounters then blob "unique-reserve-reuse-counter-fold/1".toUTF8 else ByteArray.empty)
    need (expected == (← byteField object "policy_bytes")) "runtime policy preimage disagreement"
    hashField object "policy_bytes" "policy_identity" "runtime policy"
    need ((← field object "policy_identity") == (← field report s!"{role}_policy") &&
      (← field object "identity") == (← field report s!"{role}_identity")) "runtime object summary disagreement"
    let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++
      (← checked (unhex ("00 00 " ++ (← strField graph "root") ++ " 03 00 00 00 " ++
        (if role == "main" then (if foldCounters then "03" else "01") else "02") ++ " 00 00 00")))
    need (provenance == (← byteField object "provenance")) "runtime ELF provenance disagreement"
    need ((← number object "relocations") == 0 && !(← strField object "typed_program_diagnostic").isEmpty)
      "runtime leaf artifact disagreement"

private def inspectCase (schema row snapshot : Json) (foldCounters : Bool) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-native-runtime-case/1" &&
    (← field snapshot "summary") == row) "runtime snapshot/report disagreement"
  let input ← arrField row "input"
  let count := input.size
  need (count ≤ 64) "runtime accepted excess length"
  for value in input do need ((← nat value) < 18446744073709551616) "runtime truncated a Nat"
  need ((← field row "value") == Json.arr input.reverse && (← field snapshot "source") == Json.arr input.reverse &&
    (← field snapshot "ixir0") == Json.arr input.reverse) "runtime source result disagreement"
  for stage in ["ixir1", "baseline_logical", "baseline_physical", "selected_logical", "selected_physical"] do
    let observed ← field snapshot stage
    need ((← field observed "value") == Json.arr input.reverse) s!"{stage}: runtime value disagreement"
    let reused := if stage == "selected_physical" then count else 0
    for phase in ["input", "store", "reclaimed"] do
      let store ← field observed phase
      let heap ← if stage == "ixir1" then pure store else field store "heap"
      let initial := phase == "input"
      let saved := if initial then 0 else reused
      let live := (← arrField heap "nodes").countP (· != Json.null)
      if phase != "reclaimed" then
        inspectList schema heap (← field observed (if initial then "argument" else "result")) (if initial then input else input.reverse)
      need ((← number heap "rcops") == 0) "runtime physical RC disagreement"
      need ((← number heap "allocs") + saved == (if initial then count + 1 else 2 * count + 2) &&
        (← number heap "reuses") == saved && live + (← number heap "frees") == (← number heap "allocs") &&
        live == (if phase == "reclaimed" then 0 else count + 1)) "runtime physical allocation or reclamation disagreement"
      if stage != "ixir1" then
        need ((← number store "peakLiveNodes") == count + (if initial then 1 else 2) &&
          (← number store "reusedPayloadUnits") == 2 * saved) "runtime physical peak or payload disagreement"
        for key in ["resetAttempts", "hotResets", "coldResets"] do
          need ((← number store key) == 0) "runtime shared reset disagreement"
    if stage != "ixir1" then
      need ((← number observed "control_cost") == (if stage.startsWith "selected" then 4 else 5) * count + 6 &&
        (← number observed "control_remaining") == 0 && (← number observed "heap_remaining") == 0 &&
        (← number observed "reclamation_remaining") == 0) "runtime physical control cost disagreement"
  let native ← field snapshot "native"
  need ((← number native "root") == 1 && (← field native "value") == Json.arr input.reverse) "runtime result root disagreement"
  need ((← number row "main_steps") == (if foldCounters then 30 else 42) * count + 82 &&
    (← number row "release_steps") == 17 * count + 16)
    "runtime step budget disagreement"
  for phase in ["input", "returned", "reclaimed"] do inspectHeap (← field native phase) input phase
  need ((← field native "rejections") == toJson (rejectionNames count) &&
    (← field row "rejections") == (← field native "rejections")) "runtime rejection inventory disagreement"
  inspectPrefixes native count foldCounters
  need ((← number row "prefixes") == (← arrField native "prefixes").size) "runtime prefix summary disagreement"

private def hexValue (value : String) : IO Nat := do
  let mut number := 0
  for char in value.toList do
    let some digit := hexDigit char | throw (IO.userError "invalid readelf hex offset")
    number := 16 * number + digit
  return number

private def inspectText (readelf : String) (path : FilePath) (expected : ByteArray) : IO Unit := do
  let dump ← run readelf #["-W", "-x", ".text", path.toString]
  let mut actual := ByteArray.empty
  for line in dump.splitOn "\n" do
    let parts := words line
    if !(parts.headD "").startsWith "0x" then continue
    let offset ← hexValue ((parts.headD "").drop 2).toString
    need (offset == actual.size && offset < expected.size) "readelf text offsets disagree"
    let count := min 16 (expected.size - offset)
    let row ← checked (unhex (String.join (parts.drop 1 |>.take ((count + 3) / 4))))
    need (row.size == count) "readelf text row size disagrees"
    actual := actual ++ row
  need (actual == expected) "ELF text differs from selected encoding"

private def inspectObject (directory : FilePath) (pipeline : Json) (role readelf objdump : String) : IO Unit := do
  let object ← field pipeline role
  let path := directory / (← strField object "file")
  let content ← IO.FS.readBinFile path
  need (content.size == (← number object "size") && digest content == (← strField object "identity"))
    "runtime object bytes disagree with identity"
  let elf ← inspectElf readelf path (← strField object "symbol")
  need (elf.contains "There are no relocations in this file.") "runtime object has external relocations"
  need (containsBytes content (← byteField object "provenance")) "runtime object lost exact provenance"
  inspectText readelf path (← byteField object "text")
  let disassembly ← disassemble objdump path (← strField object "symbol")
  for forbidden in ["call ", "push ", "pop ", "rsp", "rbx", "rbp", "r12", "r13", "r14", "r15"] do
    need (!disassembly.contains forbidden) s!"runtime leaf uses forbidden instruction or register: {forbidden}"

private def nativeRun (cc readelf : String) (harness directory executable : FilePath)
    (rows : Array Json) (snapshots : Array Json) : IO Unit := do
  let initializers ← rows.mapM fun row => do
    let name ← strField row "name"
    need (fileName name) "unsafe native case name"
    let values ← (← arrField row "input").mapM fun value => do return s!"UINT64_C({← nat value})"
    return "{\"" ++ name ++ "\"," ++ toString values.size ++ ",{ " ++
      (if values.isEmpty then "0" else String.intercalate "," values.toList) ++ " }}"
  IO.FS.writeFile (directory / "runtime_cases.h")
    ("static const Input inputs[] = {\n" ++ String.intercalate ",\n" initializers.toList ++ "\n};\n")
  let _ ← run cc #["-std=c11", "-O2", "-fomit-frame-pointer", "-Wall", "-Wextra", "-Werror",
    "-Wl,--fatal-warnings", "-no-pie", "-I", directory.toString, harness.toString,
    (directory / "main.o").toString, (directory / "release.o").toString, "-o", executable.toString]
  let observed ← array (← checked (Json.parse (← run executable.toString #[])))
  need (observed.size == rows.size) "linked runtime case inventory disagreement"
  for index in [:rows.size] do
    need ((← field observed[index]! "name") == (← field rows[index]! "name")) "linked runtime case order disagreement"
    let expected ← field snapshots[index]! "native"
    for key in ["input", "root", "value", "returned", "reclaimed", "rejections"] do
      need ((← field observed[index]! key) == (← field expected key)) s!"linked runtime observation differs from byte evaluator: {key}"
  let headers ← run readelf #["-W", "-l", executable.toString]
  let stacks := (headers.splitOn "\n").filter (·.contains "GNU_STACK")
  need (stacks.length == 1 && !stacks.any (·.contains "RWE")) "runtime executable stack is executable"

private def regressions (report pipeline row snapshot : Json) (foldCounters : Bool) : IO Unit := do
  for (name, path, replacement, fragment) in [
      ("ABI", ["abi", "cell_words"], toJson (3 : Nat), "runtime ABI"),
      ("word bound", ["abi", "max_length"], toJson (65 : Nat), "runtime ABI"),
      ("argument world", ["source", "argument_worlds"], toJson ["shared"], "source function contract"),
      ("policy", ["main", "policy_bytes"], toJson "00", "policy preimage"),
      ("ELF root", ["release", "provenance"], toJson "00", "ELF provenance"),
      ("role", ["release", "symbol"], toJson "compilatrix_runtime_reverse", "object role"),
      ("graph", ["ixir1", "main"], toJson "00", "graph preimage"),
      ("entry", ["entry_address"], ← field pipeline "worker_address", "function inventory")] do
    rejects s!"{name} corruption" fragment (inspectPipeline report (← replaceAt pipeline path replacement) foldCounters)
  rejects "counter-fold selector corruption" "runtime ABI"
    (inspectPipeline report (← replaceAt pipeline ["abi", "selector"]
      (toJson (if foldCounters then "unique-reverse-runtime-x86/1" else "unique-reverse-runtime-x86/2"))) foldCounters)
  rejects "counter-fold role corruption" "object version"
    (inspectPipeline report (← replaceAt pipeline ["main", "role_version"]
      (toJson (if foldCounters then (1 : Nat) else 3))) foldCounters)
  let schema ← field pipeline "schema"
  for (name, path, replacement, fragment) in [
      ("root", ["native", "root"], toJson (0 : Nat), "result root"),
      ("rejections", ["native", "rejections"], toJson ([] : List String), "rejection inventory"),
      ("physical RC", ["selected_physical", "store", "heap", "rcops"], toJson (1 : Nat), "physical RC"),
      ("peak", ["selected_physical", "store", "peakLiveNodes"], toJson (99 : Nat), "peak or payload")] do
    rejects s!"{name} corruption" fragment (inspectCase schema row (← replaceAt snapshot path replacement) foldCounters)
  let changedRow ← replaceAt row ["main_steps"] (toJson (0 : Nat))
  rejects "counter-fold step corruption" "step budget"
    (inspectCase schema changedRow (← replaceAt snapshot ["summary"] changedRow) foldCounters)
  let cells ← arrField (← field (← field snapshot "native") "returned") "cells"
  let cell ← array cells[1]!
  for (fieldIndex, replacement, fragment) in [(2, toJson (1 : Nat), "runtime pointer"), (3, toJson (1 : Nat), "runtime padding")] do
    let changed ← replaceAt snapshot ["native", "returned", "cells"] (Json.arr (cells.set! 1 (Json.arr (cell.set! fieldIndex replacement))))
    rejects "cell corruption" fragment (inspectCase schema row changed foldCounters)
  let freed ← arrField (← field (← field snapshot "native") "reclaimed") "cells"
  let changed ← replaceAt snapshot ["native", "reclaimed", "cells"] (Json.arr (freed.set! 1 cells[1]!))
  rejects "reclamation corruption" "cell not fully reclaimed" (inspectCase schema row changed foldCounters)

def main (args : List String) : IO UInt32 := cli "source native runtime check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected", "--readelf", "--objdump", "--cc", "--harness", "--variant", "--artifacts"] args)
  let some fixture := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let variant := option args "--variant" "baseline"
  need (variant == "baseline" || variant == "counter-fold") "--variant must be baseline or counter-fold"
  let foldCounters := variant == "counter-fold"
  let expected ← readJson (option args "--expected" (if foldCounters then
    "Tests/Fixtures/Compiler/source-native-runtime/expected-counter-fold.json" else "Tests/Fixtures/Compiler/source-native-runtime/expected.json"))
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  let native ← nativeArgs args
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run fixture ((if foldCounters then #["--counter-fold"] else #[]) ++ #[output.toString]))
        ["source-native-runtime ok:"] "runtime producer"
    let report ← readJson (first / "report.json")
    need (report == expected && (← strField report "format") == "compilatrix/source-native-runtime-report/1")
      "reviewed runtime source, object, resource, or rejection matrix drifted"
    let pipeline ← readJson (first / "pipeline.json")
    need ((← strField report "pipeline") == "pipeline.json" &&
      digest pipeline.compress.toUTF8 == (← strField report "pipeline_identity")) "runtime pipeline snapshot identity disagreement"
    let rows ← arrField report "cases"
    need (rows.size == 8 && (← arrField report "adapter_and_selection_rejections").size == 6) "runtime matrix inventory disagreement"
    let mut inventory := ["report.json", "pipeline.json", "main.o", "release.o"]
    for row in rows do
      let name ← strField row "snapshot"
      need (fileName name && !inventory.contains name) "invalid or duplicate runtime artifact path"
      inventory := name :: inventory
    inventory := inventory.mergeSort (· ≤ ·)
    let outputs := [first, second] ++ (optional args "--artifacts").toList.map FilePath.mk
    for output in outputs do
      let files ← output.readDir
      need ((files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "runtime artifact inventory drifted"
      for file in files do need (!(← file.path.isDir)) "unexpected runtime artifact directory"
    for name in inventory do
      for output in outputs.tail do
        need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (output / name))) s!"fresh or supplied runtime artifacts differ: {name}"
    inspectPipeline report pipeline foldCounters
    for role in ["main", "release"] do inspectObject first pipeline role readelf objdump
    let snapshots ← rows.mapM fun row => do
      let snapshot ← readJson (first / (← strField row "snapshot"))
      inspectCase (← field pipeline "schema") row snapshot foldCounters
      return snapshot
    if let some (cc, harness) := native then nativeRun cc readelf harness first (directory / "runtime-native") rows snapshots
    let some three := rows.findIdx? (fun row => (row.getObjValAs? String "name").toOption == some "three")
      | throw (IO.userError "missing runtime three-element regression")
    regressions report pipeline rows[three]! snapshots[three]! foldCounters
    let mainBytes ← IO.FS.readBinFile (first / "main.o")
    for corrupt in [mainBytes.extract 0 (mainBytes.size - 1), ← IO.FS.readBinFile (first / "release.o")] do
      IO.FS.writeBinFile (first / "main.o") corrupt
      rejects "object corruption" "object bytes disagree" (inspectObject first pipeline "main" readelf objdump)
    IO.FS.writeBinFile (first / "main.o") mainBytes
    let suffix := if native.isSome then ", one linked process runs all eight inputs" else ""
    IO.println s!"source native runtime check ok: {variant}, two fresh artifact sets, one compiled function and ELF pair, canonical provenance, 20 corruption regressions, complete reclamation{suffix}"
