import Ix.Compiler.Tools.UpstreamNativeCheck

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck
open Ix.Compiler.Tools.X86Check Ix.Compiler.Tools.UpstreamNativeCheck

def main (args : List String) : IO UInt32 := cli "source native upstream check failed" do
  if let ["inspect", directory] := args then
    let directory : FilePath := directory
    let report ← readJson (directory / "report.json")
    let rows ← arrField report "cases"
    need (rows.size == 1) "named upstream check needs one entry"
    let row := rows[0]!
    let snapshot ← readJson (directory / (← strField row "snapshot"))
    let bytes ← IO.FS.readBinFile (directory / (← strField row "object"))
    inspect row snapshot bytes
    IO.println "source native upstream named artifact check ok"
    return
  let args ← checked (parseArgs ["--fixture", "--expected", "--cc", "--harness", "--readelf", "--objdump"] args)
  let some fixture := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-native-upstream/expected.json")
  let native ← nativeArgs args
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run fixture #[output.toString]) ["source-native-upstream ok:"] "upstream native producer"
    need ((← readJson (first / "report.json")) == expected) "upstream native reviewed report drifted"
    let rows ← arrField expected "cases"
    need (rows.size == 5) "upstream native source inventory drifted"
    let mut inventory := ["report.json"]
    let mut objects := 0
    for row in rows do
      let snapshotName ← strField row "snapshot"
      need (!snapshotName.contains "/" && !snapshotName.contains "..") "unsafe upstream snapshot name"
      inventory := snapshotName :: inventory
      if (← field row "object") == Json.null then continue
      let objectName ← strField row "object"
      need (!objectName.contains "/" && !objectName.contains "..") "unsafe upstream object name"
      inventory := objectName :: inventory
      objects := objects + 1
      let snapshot ← readJson (first / snapshotName)
      let bytes ← IO.FS.readBinFile (first / objectName)
      inspect row snapshot bytes
      regressions row snapshot bytes
      let _ ← inspectElf readelf (first / objectName)
      requireAll (← disassemble objdump (first / objectName)) ["call", "add    rax,0x1"] "computational upstream object"
      if let some (cc, harness) := native then
        let value ← number (← field row "observation") "nat"
        let executable := directory / s!"native-{value}"
        let _ ← run cc #["-O3", "-fomit-frame-pointer", "-fno-lto", "-Wall", "-Wextra", "-Werror",
          s!"-DEXPECTED_RESULT={value}", harness.toString, (first / objectName).toString,
          "-Wl,-z,noexecstack", "-o", executable.toString]
        let result ← checked (Json.parse (← run executable.toString))
        need ((← number result "value") == value && (← number result "heap_allocations") == 0)
          "linked upstream native result or representation disagrees"
        for key in ["saved_registers", "stack", "caller_frame"] do
          need ((← field result key) == toJson true) s!"linked upstream native {key} failed"
    need (objects == 3) "upstream native object inventory drifted"
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      need (((← output.readDir).toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "upstream native complete file inventory drifted"
    for file in inventory do
      need ((← IO.FS.readBinFile (first / file)) == (← IO.FS.readBinFile (second / file)))
        s!"fresh upstream native artifact differs: {file}"
    IO.println "source native upstream check ok: five unchanged entries, two fresh complete artifact sets, three computational objects, capture transport/corruption/fallback and ABI checks"
