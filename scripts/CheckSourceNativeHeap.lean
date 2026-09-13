import Compilatrix.Tools.HeapNativeCheck
import Compilatrix.Tools.X86Check

open Lean System Compilatrix.Tools.Check Compilatrix.Tools.UniqueCheck
open Compilatrix.Tools.X86Check Compilatrix.Tools.HeapNativeCheck

private def reloadReject (consumer : String) (wire : FilePath) (root entry mode : String) (output : FilePath) (extra : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := consumer, args := #[wire.toString, root, entry, mode, output.toString] ++ extra }
  need (result.exitCode != 0 && (result.stdout ++ result.stderr).contains "heap snapshot object failed" && !(← output.pathExists))
    "heap fresh consumer accepted corrupt bytes/entry metadata"

def main (args : List String) : IO UInt32 := cli "source native heap check failed" do
  let args ← checked (parseArgs ["--fixture", "--consumer", "--expected", "--cc", "--harness", "--readelf", "--objdump", "--emission"] args)
  let some fixture := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let some consumer := optional args "--consumer" | throw (IO.userError "--consumer is required")
  let expected ← readJson (option args "--expected" "fixtures/source-native-heap/expected.json")
  let emission := option args "--emission" "tree"
  need (emission == "tree" || emission == "shared" || emission == "graph") "unknown heap emission mode"
  let extra := if emission == "tree" then #[] else #[emission]
  let native ← nativeArgs args
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run fixture (#[output.toString] ++ extra)) ["source native heap ok:"] "heap source producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "heap reviewed report drifted"
    need ((← strField report "format") == "compilatrix/source-native-heap-report/1" &&
      (← strField report "policy") == "physical-leaf-cfg/1" &&
      (← number report "source_evaluations") == 95 && (← number report "object_executions") == 171 &&
      (← number report "snapshot_roundtrips") == 9 && (← number report "legacy_policy_rejections") == 2)
      "heap report inventory disagrees"
    need ((← field report "admission_rejections") == toJson (["arena-overflow", "shared-node-retain", "nested-heap-field",
      "borrowed-parameter", "three-field-leaf", "missing-schema", "missing-callee", "recursive-call", "cyclic-block",
      "value-slots", "duplicate-owner", "duplicate-credit", "reuse-layout", "nat-overflow", "pap-in-body",
      "higher-order-apply", "external-call", "edge-copies", "cfg-expansion"] : List String)) "heap admission inventory drifted"
    if emission == "graph" then
      let original ← arrField report "admission_rejections"
      need ((← field report "graph_admission_rejections") == toJson (original.filter (· != toJson "cfg-expansion")) &&
        (← field report "graph_expansion_accepted") == toJson true) "heap graph admission inventory drifted"
    let rows ← arrField expected "cases"
    need (rows.size == names.size) "heap source/physical inventory drifted"
    let mut inventory := ["report.json"]
    let mut corruptionCount := 0
    let mut nativeCalls := 0
    for index in [:rows.size] do
      let row := rows[index]!
      let name ← strField row "name"
      need (name == names[index]!) "heap family order drifted"
      let snapshotName := s!"{name}.json"
      let objectName := s!"{name}.o"
      let wireName := s!"{name}.ixir2"
      inventory := snapshotName :: objectName :: wireName :: inventory
      if emission == "shared" then
        need ((← strField row "emission") == "heap-block-sharing/1") "heap shared emission policy disagrees"
      if emission == "graph" then
        need ((← strField row "emission") == "heap-cfg-graph/1") "heap graph emission policy disagrees"
      let snapshot ← readJson (first / snapshotName)
      let bytes ← IO.FS.readBinFile (first / objectName)
      let wire ← IO.FS.readBinFile (first / wireName)
      inspect row snapshot bytes wire (emission == "shared") (emission == "graph")
      corruptionCount := corruptionCount + (← regressions row snapshot bytes wire (emission == "shared") (emission == "graph"))
      let elf ← inspectElf readelf (first / objectName) "compilatrix_heap_cfg"
      requireAll elf ["There are no relocations"] "heap local-call object"
      let assembly ← disassemble objdump (first / objectName) "compilatrix_heap_cfg"
      requireAll assembly ["push", "pop", "rbp", "r15", "rdi", "rdx", "call", "cmp", "ja", "jb", "ret"] "heap ABI/guard instructions"
      if arity name == 2 then requireAll assembly ["rsi"] "heap second argument"
      let root ← strField row "root"
      let entry ← strField row "entry"
      let mode ← strField row "origin"
      let reloaded := directory / s!"reloaded-{name}.o"
      requireAll (← run consumer (#[(first / wireName).toString, root, entry, mode, reloaded.toString] ++ extra))
        ["heap snapshot object ok:"] "heap persisted-only consumer"
      need ((← IO.FS.readBinFile reloaded) == bytes) "heap fresh consumer changed the ELF"
      let badOutput := directory / s!"rejected-{name}.o"
      let zero := String.ofList (List.replicate 64 '0')
      reloadReject consumer (first / wireName) zero entry mode badOutput extra
      reloadReject consumer (first / wireName) root zero mode badOutput extra
      let corrupt := directory / s!"corrupt-{name}.ixir2"
      IO.FS.writeBinFile corrupt (wire.extract 0 (wire.size - 1))
      reloadReject consumer corrupt root entry mode badOutput extra
      IO.FS.writeBinFile corrupt (wire.set! (wire.size - 1) (wire[wire.size - 1]! ^^^ 1))
      reloadReject consumer corrupt root entry mode badOutput extra
      if let some (cc, harness) := native then
        let executable := directory / s!"native-{name}"
        let depth ← number row "stack_depth"
        let _ ← run cc #["-O2", "-fomit-frame-pointer", "-fno-lto", "-Wall", "-Wextra", "-Werror",
          s!"-DFAMILY={index}", s!"-DSTACK_DEPTH={depth}", harness.toString, (first / objectName).toString,
          "-Wl,-z,noexecstack", "-Wl,--fatal-warnings", "-o", executable.toString]
        let result ← checked (Json.parse (← run executable.toString))
        need ((← number result "calls") == 86) "heap native call inventory changed"
        nativeCalls := nativeCalls + (← number result "calls")
        for key in ["saved_registers", "stack", "caller_frame", "finite_workspace", "exact_counters", "reclaimed", "capacity_rejected"] do
          need ((← field result key) == toJson true) s!"heap native {key} failed"
        let headers ← run readelf #["-W", "-l", executable.toString]
        let stacks := (headers.splitOn "\n").filter (·.contains "GNU_STACK")
        need (stacks.length == 1 && !stacks.any (·.contains "RWE")) "heap executable stack policy changed"
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      need (((← output.readDir).toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "heap complete file inventory drifted"
    for file in inventory do
      need ((← IO.FS.readBinFile (first / file)) == (← IO.FS.readBinFile (second / file))) s!"fresh heap artifact differs: {file}"
    let alteredRow ← replaceAt rows[0]! ["root"] (toJson (String.ofList (List.replicate 64 '0')))
    let alteredReport ← replaceAt report ["cases"] (toJson (rows.set! 0 alteredRow))
    rejects "heap identical producer corruption" "reviewed report" (need (alteredReport == expected) "heap reviewed report drifted")
    IO.println s!"source native heap check ok: five source and four physical CFGs, 95 source applications, 171 ELF runs, nine persisted-only reloads, {corruptionCount + 1} independent corruptions, 36 reload rejections, {nativeCalls} native calls"
