import Benchmarks.Compiler.Build

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def inspectBuild (build : FilePath) : IO Json := do
  checkData
  let metadata ← readJson (build / "build.json")
  need ((← strField metadata "format") == "compilatrix/benchmark-build/1") "unknown benchmark build format"
  for (name, key) in [("manifest.json", "manifest_blake3"), ("toolchains.json", "toolchains_blake3")] do
    need (digest (← IO.FS.readBinFile (build / name)) == (← strField metadata key)) s!"{name} changed after build"
  need ((← IO.FS.readBinFile (build / "datasets/datasets.bin")) == datasetBytes &&
    (← readJson (build / "datasets/datasets.json")) == datasetJson &&
    (← strField metadata "datasets_blake3") == digest datasetBytes) "benchmark datasets changed or disagree with oracle"
  inspectFiles (build / "artifacts") (← field metadata "artifacts")
  inspectFiles (build / "bin") (← field metadata "executables")
  inspectFiles (build / "tools-bin") (← field metadata "tools")
  need (digest (← IO.FS.readBinFile (build / "tool-identities.json")) == (← strField metadata "tool_identities_blake3"))
    "tool identity inventory changed"
  return metadata

def originalHarness (build output : FilePath) (tools : Toolchains) : IO Json := do
  let n2 := build / "artifacts/compilatrix"
  let report ← readJson (n2 / "report.json")
  let rows ← arrField report "cases"
  let initializers ← rows.mapM fun row => do
    let name ← strField row "name"
    let values ← (← arrField row "input").mapM fun value => do return s!"UINT64_C({← nat value})"
    return "{\"" ++ name ++ "\"," ++ toString values.size ++ ",{ " ++
      (if values.isEmpty then "0" else String.intercalate "," values.toList) ++ " }}"
  IO.FS.writeFile (output / "runtime_cases.h")
    ("static const Input inputs[] = {\n" ++ String.intercalate ",\n" initializers.toList ++ "\n};\n")
  let mut summaries := #[]
  for implementation in ["compilatrix", "compcert", "gcc", "clang"] do
    let objects := if implementation == "compilatrix" then #[(n2 / "main.o").toString, (n2 / "release.o").toString]
      else #[(build / s!"artifacts/{implementation}/kernel.o").toString]
    let binary := output / s!"original-{implementation}"
    let _ ← logged (output / "logs") s!"original-link-{implementation}" tools.gcc
      (#["-std=c11", "-O2", "-fomit-frame-pointer", "-Wall", "-Wextra", "-Werror", "-no-pie",
        "-I", output.toString, "Tests/Fixtures/Compiler/source-native-runtime/native_harness.c"] ++ objects ++
        #["-Wl,-z,noexecstack", "-o", binary.toString]) #[] none tools.timerTool
    let result ← logged (output / "logs") s!"original-run-{implementation}" binary.toString #[] #[] none tools.timerTool
    let observed ← array (← checked (Json.parse result))
    need (observed.size == rows.size) "original native matrix incomplete"
    let mut rejections := 0
    for index in [:rows.size] do
      let expected ← field (← readJson (n2 / (← strField rows[index]! "snapshot"))) "native"
      need ((← field observed[index]! "name") == (← field rows[index]! "name")) "original native case name drifted"
      for key in ["input", "root", "value", "returned", "reclaimed", "rejections"] do
        need ((← field observed[index]! key) == (← field expected key)) s!"{implementation}: original byte/native {key} disagreement"
      rejections := rejections + (← arrField observed[index]! "rejections").size
    need (rejections == 203) "original malformed input inventory drifted"
    summaries := summaries.push (Json.mkObj [("implementation", toJson implementation),
      ("successful_inputs", toJson rows.size), ("malformed_inputs", toJson rejections),
      ("observations_blake3", toJson (digest (Json.arr observed).compress.toUTF8))])
  return Json.arr summaries

def malformedDatasets (build output : FilePath) : IO Json := do
  let cases : Array (String × ByteArray × String) := #[
    ("magic", datasetBytes.set! 0 0, "wrong binary magic"),
    ("count", datasetBytes.set! 8 0, "wrong dataset inventory"),
    ("metadata", datasetBytes.set! 16 1, "noncanonical dataset metadata"),
    ("padding", datasetBytes.set! 48 1, "nonzero dataset padding"),
    ("trailing", datasetBytes.push 0, "trailing binary input"),
    ("truncated", datasetBytes.extract 0 (datasetBytes.size - 1), "truncated binary input")]
  let mut results := #[]
  for (name, bytes, expected) in cases do
    let path := output / s!"bad-{name}.bin"
    IO.FS.writeBinFile path bytes
    for implementation in implementations do
      let result ← IO.Process.output {
        cmd := (build / s!"bin/{implementation}").toString
        args := #[implementation, "verify", path.toString]
        env := runtimeEnv }
      need (result.exitCode != 0 && result.stderr.contains expected) s!"{implementation} accepted malformed dataset {name}"
      results := results.push (Json.mkObj [("implementation", toJson implementation), ("case", toJson name),
        ("exit_code", toJson result.exitCode.toNat), ("stderr", toJson result.stderr)])
  return Json.arr results

def verifySuite (build output : FilePath) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  fresh output
  let metadata ← inspectBuild build
  let tools ← checked (fromJson? (← field metadata "tool_commands") : Except String Toolchains)
  let mut summaries := #[]
  let mut arenaIdentity : Option Json := none
  for implementation in implementations do
    let result ← logged (output / "logs") s!"matrix-{implementation}" (build / s!"bin/{implementation}").toString
      #[implementation, "verify", (build / "datasets/datasets.bin").toString] runtimeEnv none tools.timerTool
    IO.FS.writeFile (output / s!"{implementation}.jsonl") result
    let rows ← readLines (output / s!"{implementation}.jsonl")
    let before ← IO.monoNanosNow
    let summary ← inspectMatrix implementation rows
    checkerRegressions implementation rows
    let checkNs := (← IO.monoNanosNow) - before
    if isArena implementation then
      let identity ← field summary "matrix_blake3"
      if let some expected := arenaIdentity then need (identity == expected) "matched arena complete observations differ"
      arenaIdentity := some identity
    summaries := summaries.push (Json.mkObj [("result", summary), ("independent_check_ns", toJson checkNs)])
    IO.println s!"benchmark verify: {implementation} complete matrix checked"
  let original ← originalHarness build output tools
  let binaryNegatives ← malformedDatasets build output
  -- Check the artifacts again after every executable and diagnostic has run.
  let _ ← inspectBuild build
  writeJson (output / "correctness.json") (Json.mkObj [
    ("format", toJson "compilatrix/benchmark-correctness/1"), ("build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))),
    ("executables", ← field metadata "executables"), ("matrices", Json.arr summaries),
    ("original_native_matrix", original), ("malformed_datasets", binaryNegatives),
    ("word_overflow_rejected", toJson true), ("full_values", toJson true), ("status", toJson "passed")])
  IO.println "benchmark verify: six implementations, original ABI/rejection matrix, malformed inputs, and checker corruptions passed"

end Benchmarks.Compiler
