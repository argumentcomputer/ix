import Ix.Compiler.Tools.ScalarNativeCheck
import Ix.Compiler.Tools.X86Check

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck
open Ix.Compiler.Tools.X86Check Ix.Compiler.Tools.ScalarNativeCheck

def main (args : List String) : IO UInt32 := cli "source native scalar check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected", "--cc", "--harness", "--readelf", "--objdump"] args)
  let some fixture := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-native-scalar/expected.json")
  let native ← nativeArgs args
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run fixture #[output.toString]) ["source-native-scalar ok:"] "scalar source producer"
    need ((← readJson (first / "report.json")) == expected) "scalar reviewed report drifted"
    let rows ← arrField expected "cases"
    need (rows.size == 5) "scalar source inventory drifted"
    let mut inventory := ["report.json"]
    for index in [:rows.size] do
      let row := rows[index]!
      let name ← strField row "name"
      need (name == #["add", "sub", "diamond", "helpers", "nested"][index]!) "scalar family order drifted"
      let snapshotName ← strField row "snapshot"
      let objectName ← strField row "object"
      need (snapshotName == s!"{name}.json" && objectName == s!"{name}.o") "unsafe scalar artifact name"
      inventory := snapshotName :: objectName :: inventory
      let snapshot ← readJson (first / snapshotName)
      let bytes ← IO.FS.readBinFile (first / objectName)
      inspect row snapshot bytes
      regressions row snapshot bytes
      let elf ← inspectElf readelf (first / objectName) "compilatrix_scalar"
      requireAll elf ["There are no relocations"] "scalar local-call object"
      let assembly ← disassemble objdump (first / objectName) "compilatrix_scalar"
      requireAll assembly ["push", "rbp", "rdi", "rsi", "ret"] "scalar ABI instructions"
      if index == 3 || index == 4 then requireAll assembly ["call"] "scalar helper calls"
      if let some (cc, harness) := native then
        let executable := directory / s!"native-{name}"
        let depth ← number row "stack_depth"
        let _ ← run cc #["-O2", "-fomit-frame-pointer", "-fno-lto", "-Wall", "-Wextra", "-Werror",
          s!"-DFAMILY={index}", s!"-DSTACK_DEPTH={depth}", harness.toString, (first / objectName).toString,
          "-Wl,-z,noexecstack", "-Wl,--fatal-warnings", "-o", executable.toString]
        let result ← checked (Json.parse (← run executable.toString))
        need ((← number result "calls") == 166) "scalar native call inventory changed"
        for key in ["saved_registers", "stack", "caller_frame", "guarded_stack"] do
          need ((← field result key) == toJson true) s!"scalar native {key} failed"
        let headers ← run readelf #["-W", "-l", executable.toString]
        let stacks := (headers.splitOn "\n").filter (·.contains "GNU_STACK")
        need (stacks.length == 1 && !stacks.any (·.contains "RWE")) "scalar executable stack policy changed"
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      need (((← output.readDir).toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "scalar complete file inventory drifted"
    for file in inventory do
      need ((← IO.FS.readBinFile (first / file)) == (← IO.FS.readBinFile (second / file))) s!"fresh scalar artifact differs: {file}"
    IO.println "source native scalar check ok: five fresh source artifacts, 95 object runs, 25 corruption checks, native ABI and guarded stack checks"
