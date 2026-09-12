import Compilatrix.Tools.HeapNativeCheck
import Compilatrix.Tools.X86Check

/-! Independent persisted-byte and linked-native checks. This import closure
contains no compiler, native emitter, encoder, or machine evaluator. -/
namespace Compilatrix.Tools.NativeSharingCheck
open Lean System Check UniqueCheck X86Check UpstreamNativeCheck

private def inspect (row : Json) (object wire : ByteArray) : IO Unit := do
  let count ← number row "joins"
  let mode ← strField row "mode"
  need (mode == "tree" || mode == "shared") "unknown native sharing mode"
  need ((← strField row "case") == s!"joins-{count}-{mode}" && (← strField row "origin") == "checked-ixir2" &&
    (← strField row "emission") == (if mode == "shared" then "heap-block-sharing/1" else "heap-block-tree/1"))
    "native sharing policy/origin disagrees"
  need (wire.size == (← number row "snapshot_bytes") && IxIR2Check.root wire == (← strField row "snapshot_root"))
    "native sharing snapshot identity disagrees"
  let artifact ← checked (IxIR2Check.decode wire)
  need ((← strField (← field artifact "policy") "lowering") == "compiler-scaling-joins/1" &&
    (← arrField artifact "dependencies").isEmpty && (← arrField artifact "schemas").isEmpty &&
    (← arrField artifact "layouts").isEmpty && (← arrField artifact "scalarLeaves").isEmpty)
    "native sharing fixture provenance changed"
  let declarations ← arrField (← field artifact "program") "declarations"
  need (declarations.size == 1 && (← strField declarations[0]! "address") == (← strField row "entry"))
    "native sharing declaration/entry changed"
  let declaration ← arrField declarations[0]! "declaration"
  need (declaration.size == 2 && declaration[0]! == toJson "fn") "native sharing function changed"
  need ((← arrField declaration[1]! "blocks").size == 3 * count + 1 &&
    (← number row "input_blocks") == 3 * count + 1 && (← number row "function_count") == 1 &&
    (← number row "allocation_bound") == 0) "native sharing fixed CFG shape changed"
  need (object.size == (← number row "elf_bytes") && IxIR2Check.root object == (← strField row "elf_root"))
    "native sharing ELF identity disagrees"
  let table ← readLE object 40 8
  let offset ← readLE object (table + 64 + 24) 8
  let size ← readLE object (table + 64 + 32) 8
  let text ← slice object offset size
  need (text.size == (← number row "text_bytes") && IxIR2Check.root text == (← strField row "text_root"))
    "native sharing text identity disagrees"
  let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 01 " ++ (← strField row "snapshot_root"))))
  HeapNativeCheck.inspectObject object text provenance (← number row "entry_offset") "compilatrix_scaling"
  let blocks ← number row "x86_blocks"
  need ((← number row "mutation_rejections") == (if mode == "shared" then 2 * blocks + 1 else 0))
    "native sharing mutation inventory changed"
  let observations ← arrField row "observations"
  need (observations.size == 6) "native sharing semantic inventory changed"
  for i in [:observations.size] do
    let argument := #[0, 1, count - 1, count, count + 1, 2^64 - 1][i]!
    need ((← number observations[i]! "argument") == argument && (← number observations[i]! "value") == argument - count)
      "native sharing formula disagrees"

private def regressions (row : Json) (object wire : ByteArray) : IO Nat := do
  rejects "sharing object byte" "ELF identity" (inspect row (object.set! 0 0) wire)
  rejects "sharing wire byte" "snapshot identity" (inspect row object (wire.set! 0 0))
  rejects "sharing truncated wire" "snapshot identity" (inspect row object (wire.extract 0 (wire.size - 1)))
  rejects "sharing mode" "unknown native sharing mode" (inspect (← replaceAt row ["mode"] (toJson "unreviewed")) object wire)
  rejects "sharing source claim" "policy/origin" (inspect (← replaceAt row ["origin"] (toJson "source")) object wire)
  let observations ← arrField row "observations"
  let changed ← replaceAt observations[0]! ["value"] (toJson (42 : Nat))
  rejects "sharing result" "formula" (inspect (← replaceAt row ["observations"] (toJson (observations.set! 0 changed))) object wire)
  return 6

private def checkDirectory (directory temporary : FilePath) (expected : Json) (consumer readelf objdump : String)
    (native : Option (String × FilePath)) : IO Json := do
  let report ← readJson (directory / "report.json")
  need (report == expected) "native sharing reviewed report drifted"
  need ((← strField report "format") == "compilatrix/native-sharing/1" &&
    (← number report "rejected_joins") == 10 && (← strField report "rejection") == "heap CFG entry has no admitted scalar-argument interface")
    "native sharing rejection boundary changed"
  need ((← field report "selection_limits") == Json.mkObj [("depth", toJson (128 : Nat)), ("work", toJson (4096 : Nat)),
    ("functions", toJson (32 : Nat)), ("allocations", toJson (64 : Nat)), ("values", toJson (16 : Nat)),
    ("credits", toJson (4 : Nat)), ("copies", toJson (12 : Nat))]) "native sharing compiler limits changed"
  let rows ← arrField report "cases"
  let mut inventory := ["report.json", "measurements.json"]
  let mut corruptionCount := 0
  let mut nativeCalls := 0
  for row in rows do
    let label ← strField row "case"
    let count ← number row "joins"
    let mode ← strField row "mode"
    let extra := if mode == "shared" then #["shared"] else #[]
    let objectPath := directory / s!"{label}.o"
    let wirePath := directory / s!"{label}.ixir2"
    let object ← IO.FS.readBinFile objectPath
    let wire ← IO.FS.readBinFile wirePath
    need ((← readJson (directory / s!"{label}.json")) == row) "native sharing persisted row changed"
    inspect row object wire
    corruptionCount := corruptionCount + (← regressions row object wire)
    inventory := s!"{label}.o" :: s!"{label}.ixir2" :: s!"{label}.json" :: inventory
    let elf ← inspectElf readelf objectPath "compilatrix_scaling"
    requireAll elf ["There are no relocations"] "shared local control"
    let assembly ← disassemble objdump objectPath "compilatrix_scaling"
    requireAll assembly ["push", "pop", "call", "jmp", "cmp", "rbp", "r15"] "shared native control"
    let reloaded := temporary / s!"{label}.o"
    let root ← strField row "snapshot_root"
    let entry ← strField row "entry"
    requireAll (← run consumer (#[wirePath.toString, root, entry, "export", reloaded.toString] ++ extra ++
      #["--name", "compilatrix_scaling"])) ["heap snapshot object ok:"] "native sharing persisted-only replay"
    need ((← IO.FS.readBinFile reloaded) == object) "native sharing replay changed exact ELF bytes"
    if let some (cc, harness) := native then
      let executable := temporary / label
      let _ ← run cc #["-O2", "-fomit-frame-pointer", "-fno-lto", "-Wall", "-Wextra", "-Werror",
        harness.toString, objectPath.toString, "-Wl,-z,noexecstack", "-Wl,--fatal-warnings", "-o", executable.toString]
      let result ← checked (Json.parse (← run executable.toString #["joins", toString count]))
      need ((← number result "calls") == 33) "native sharing linked-call inventory changed"
      nativeCalls := nativeCalls + 33
      for key in ["values", "saved_registers", "finite_workspace", "exact_counters", "reclaimed", "capacity_rejected"] do
        need ((← field result key) == toJson true) s!"native sharing {key} failed"
      let headers ← run readelf #["-W", "-l", executable.toString]
      let stacks := (headers.splitOn "\n").filter (·.contains "GNU_STACK")
      need (stacks.length == 1 && !stacks.any (·.contains "RWE")) "native sharing executable stack policy changed"
  need (((← directory.readDir).toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory.mergeSort (· ≤ ·))
    "native sharing complete file inventory changed"
  let measurements ← readJson (directory / "measurements.json")
  let stages ← arrField measurements "stages"
  need ((← strField measurements "format") == "compilatrix/native-sharing-measurements/1" && stages.size == rows.size * 8)
    "native sharing measurement inventory changed"
  for row in rows do
    let label ← strField row "case"
    let measured ← stages.filterM fun item => return (← strField item "case") == label
    let names ← measured.mapM fun item => strField item "stage"
    need (names == #["snapshot-encode-check", "snapshot-decode-check", "native-export", "native-select",
      "native-emit", "native-certificate-check", "x86-encode-check", "elf-write-check"]) "native sharing stage order changed"
    for item in measured do let _ ← number item "ns"
  return Json.mkObj [("passed", toJson true), ("objects", toJson rows.size), ("persisted_replays", toJson rows.size),
    ("independent_corruptions", toJson corruptionCount), ("native_calls", toJson nativeCalls)]

def runCheck (args : List String) : IO Unit := do
  let args ← checked (parseArgs ["--fixture", "--consumer", "--expected", "--directory", "--output",
    "--cc", "--harness", "--readelf", "--objdump"] args)
  let expected ← readJson (option args "--expected" "fixtures/native-sharing/expected.json")
  let consumer := option args "--consumer" ".lake/build/bin/heap-snapshot-object"
  let fixture := option args "--fixture" ".lake/build/bin/native-sharing"
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  let native ← nativeArgs args
  IO.FS.withTempDir fun temporary => do
    let result ← if let some directory := optional args "--directory" then
        checkDirectory directory temporary expected consumer readelf objdump native
      else do
        let profile ← strField expected "profile"
        let first := temporary / "first"
        let second := temporary / "second"
        for directory in [first, second] do
          requireAll (← run fixture #[directory.toString, profile]) ["native sharing ok:"] "native sharing producer"
        for entry in ← first.readDir do
          if entry.fileName == "measurements.json" then continue
          need ((← IO.FS.readBinFile entry.path) == (← IO.FS.readBinFile (second / entry.fileName)))
            s!"native sharing fresh bytes differ: {entry.fileName}"
        need ((← second.readDir).size == (← first.readDir).size) "native sharing fresh inventory differs"
        checkDirectory first temporary expected consumer readelf objdump native
    if let some output := optional args "--output" then
      need (!(← FilePath.pathExists output)) "native sharing validation output exists"
      IO.FS.writeFile output (result.pretty ++ "\n")
    IO.println s!"native sharing check ok: {result.compress}"

end Compilatrix.Tools.NativeSharingCheck
