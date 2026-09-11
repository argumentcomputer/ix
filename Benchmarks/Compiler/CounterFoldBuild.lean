import Benchmarks.Compiler.Schedule

namespace Benchmarks.Compiler.CounterFold
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def variants : Array String := #["baseline", "counter-fold"]

def inspectBuild (build : FilePath) : IO Json := do
  checkData
  let metadata ← readJson (build / "build.json")
  need ((← strField metadata "format") == "compilatrix/counter-fold-build/1" &&
    (← field metadata "variants") == toJson variants) "counter-fold build policy disagrees"
  need ((← IO.FS.readBinFile (build / "datasets/datasets.bin")) == datasetBytes &&
    (← readJson (build / "datasets/datasets.json")) == datasetJson &&
    (← strField metadata "datasets_blake3") == digest datasetBytes) "counter-fold dataset drift"
  for (directory, key) in [("artifacts", "artifacts"), ("bin", "executables"), ("tools-bin", "tools"), ("goldens", "goldens")] do
    inspectFiles (build / directory) (← field metadata key)
  need (digest (← IO.FS.readBinFile (build / "tool-identities.json")) == (← strField metadata "tool_identities_blake3") &&
    digest (← IO.FS.readBinFile (build / "protocol.md")) == (← strField metadata "protocol_blake3")) "counter-fold tool/protocol drift"
  let baseline ← readJson (build / "artifacts/baseline/report.json")
  let folded ← readJson (build / "artifacts/counter-fold/report.json")
  for variant in variants do
    need ((← readJson (build / s!"artifacts/{variant}/report.json")) ==
      (← readJson (build / s!"goldens/{variant}.json"))) "counter-fold artifact differs from reviewed golden"
  for key in ["source_identity", "ixir1_root", "adapter_and_selection_rejections"] do
    need ((← field baseline key) == (← field folded key)) "paired source or fallback behavior differs"
  let original ← arrField baseline "cases"
  let improved ← arrField folded "cases"
  need (original.size == 8 && improved.size == 8) "paired artifact case inventory disagrees"
  for i in [:8] do
    for key in ["name", "input", "value", "release_steps", "rejections"] do
      need ((← field original[i]! key) == (← field improved[i]! key)) "paired artifact semantics differ"
    let count := (← arrField original[i]! "input").size
    need ((← number original[i]! "main_steps") == 42 * count + 82 &&
      (← number improved[i]! "main_steps") == 30 * count + 82) "paired instruction cost disagrees"
  return metadata

def buildSuite (output : FilePath) (gcc : String := "gcc") (timerTool : String := "time") : IO Unit := do
  let output ← absolute output
  fresh output
  for directory in ["bin", "artifacts/driver", "tools-bin", "goldens", "diagnostics/build"] do
    IO.FS.createDirAll (output / directory)
  writeDatasets (output / "datasets")
  IO.FS.writeFile (output / "protocol.md") (← IO.FS.readFile "Benchmarks/Compiler/counter-fold.md")
  let logs := output / "diagnostics/build"
  let flags := cFlags ++ #[s!"-ffile-prefix-map={output}=/counter-fold-build"]
  let version ← logged logs "gcc-version" gcc #["--version"] #[] none timerTool
  need (version.contains "14.3.0") "counter-fold requires pinned GCC 14.3.0"
  let _ ← logged logs "worker-launcher" gcc
    (flags ++ #["-Wall", "-Wextra", "-Werror", "Benchmarks/Compiler/native/worker_launcher.c", "-o", (output / "bin/worker-launcher").toString]) #[] none timerTool
  for name in ["common", "driver", "arena_backend"] do
    let _ ← logged logs s!"driver-{name}" gcc (flags ++ #["-Wall", "-Wextra", "-Werror", "-c",
      s!"Benchmarks/Compiler/native/{name}.c", "-o", (output / s!"artifacts/driver/{name}.o").toString]) #[] none timerTool
  let driver := #["common", "driver", "arena_backend"].map fun name => (output / s!"artifacts/driver/{name}.o").toString
  for variant in variants do
    let artifacts := output / s!"artifacts/{variant}"
    let options := if variant == "counter-fold" then #["--counter-fold"] else #[]
    let _ ← logged logs s!"produce-{variant}" ".lake/build/bin/compiler-source-native-runtime" (options ++ #[artifacts.toString]) #[] none timerTool
    let expected := if variant == "counter-fold" then "expected-counter-fold.json" else "expected.json"
    IO.FS.writeFile (output / s!"goldens/{variant}.json") (← IO.FS.readFile s!"Tests/Fixtures/Compiler/source-native-runtime/{expected}")
    let _ ← logged logs s!"independent-gate-{variant}" ".lake/build/bin/compiler-check-source-native-runtime"
      #["--fixture", ".lake/build/bin/compiler-source-native-runtime", "--variant", variant, "--artifacts", artifacts.toString, "--cc", gcc,
        "--harness", "Tests/Fixtures/Compiler/source-native-runtime/native_harness.c"] #[] none timerTool
    let _ ← logged logs s!"link-{variant}" gcc (flags ++ driver ++
      #[(artifacts / "main.o").toString, (artifacts / "release.o").toString,
        "-Wl,-z,noexecstack", "-o", (output / s!"bin/{variant}").toString]) #[] none timerTool
    for role in ["main", "release"] do
      let _ ← logged logs s!"size-{variant}-{role}" "size" #["-A", (artifacts / s!"{role}.o").toString] #[] none timerTool
      let _ ← logged logs s!"disassembly-{variant}-{role}" "objdump" #["-d", (artifacts / s!"{role}.o").toString] #[] none timerTool
    let _ ← logged logs s!"size-{variant}" "size" #["-A", (output / s!"bin/{variant}").toString] #[] none timerTool
    let _ ← logged logs s!"dependencies-{variant}" "ldd" #[(output / s!"bin/{variant}").toString] #[] none timerTool
  let mut identities := #[]
  let mut roots : Array String := #[]
  for (name, command) in [("gcc", gcc), ("lean", "lean"), ("lake", "lake"), ("time", timerTool)] do
    let path := (← run "which" #[command]).trimAscii.toString
    let resolved := (← run "readlink" #["-f", path]).trimAscii.toString
    identities := identities.push (Json.mkObj [("name", toJson name), ("resolved", toJson resolved),
      ("blake3", toJson (digest (← IO.FS.readBinFile resolved)))])
    if resolved.startsWith "/nix/store/" then
      let root := String.intercalate "/" ((resolved.splitOn "/").take 4)
      if !roots.contains root then roots := roots.push root
  writeJson (output / "tool-identities.json") (Json.arr identities)
  let closure ← IO.Process.output { cmd := "nix-store", args := #["--query", "--requisites"] ++ roots }
  IO.FS.writeFile (output / "nix-closure.txt") closure.stdout
  writeJson (output / "nix-closure-status.json") (Json.mkObj [("roots", toJson roots),
    ("exit_code", toJson closure.exitCode.toNat), ("stderr", toJson closure.stderr)])
  for name in ["benchmark", "source-native-runtime", "check-source-native-runtime"] do
    let _ ← run "cp" #[s!".lake/build/bin/compiler-{name}", (output / s!"tools-bin/compiler-{name}").toString]
  writeJson (output / "build.json") (Json.mkObj [
    ("format", toJson "compilatrix/counter-fold-build/1"), ("variants", toJson variants),
    ("gcc", toJson gcc), ("timer_tool", toJson timerTool), ("gcc_version", toJson version),
    ("build_environment", toJson (← buildEnvNames.mapM fun name => do return (name, ← IO.getEnv name))),
    ("datasets_blake3", toJson (digest datasetBytes)), ("artifacts", ← recordFiles (output / "artifacts")),
    ("executables", ← recordFiles (output / "bin")), ("tools", ← recordFiles (output / "tools-bin")),
    ("goldens", ← recordFiles (output / "goldens")),
    ("tool_identities_blake3", toJson (digest (← IO.FS.readBinFile (output / "tool-identities.json")))),
    ("protocol_blake3", toJson (digest (← IO.FS.readBinFile (output / "protocol.md"))))])
  let _ ← inspectBuild output
  let _ ← sourceSnapshot output
  IO.println s!"counter-fold build: two checked variants, identical driver objects, retained source and native artifacts in {output}"

def runScheduled (build output : FilePath) (variant : String) (schedule : Schedule) (core : Nat) : IO (Array Json) := do
  need (variants.contains variant) "unknown counter-fold variant"
  writeSchedule (output.withExtension "bin") schedule
  let result ← streamed { cmd := "taskset", args := #["--cpu-list", toString core,
    (build / "bin/worker-launcher").toString, (build / s!"bin/{variant}").toString,
    "compilatrix", "run", (build / "datasets/datasets.bin").toString, (output.withExtension "bin").toString], env := runtimeEnv } output
  IO.FS.writeFile (output.withExtension "stderr") result.stderr
  writeJson (output.withExtension "process.json") (Json.mkObj [("variant", toJson variant),
    ("executable_blake3", toJson (digest (← IO.FS.readBinFile (build / s!"bin/{variant}")))),
    ("exit_code", toJson result.exitCode.toNat), ("core", toJson core), ("schedule", toJson schedule),
    ("schedule_blake3", toJson (digest schedule.bytes)), ("stdout_blake3", toJson (digest result.stdout.toUTF8))])
  need (result.exitCode == 0) s!"counter-fold {variant} failed: {result.stderr}"
  inspectRun "compilatrix" schedule (← readLines output) (schedule.mode == 2)

def verifySuite (build output : FilePath) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  fresh output
  let metadata ← inspectBuild build
  let timer ← strField metadata "timer_tool"
  let mut summaries := #[]
  let mut matrixIdentity : Option Json := none
  for variant in variants do
    let result ← logged (output / "logs") s!"matrix-{variant}" (build / s!"bin/{variant}").toString
      #["compilatrix", "verify", (build / "datasets/datasets.bin").toString] runtimeEnv none timer
    IO.FS.writeFile (output / s!"{variant}.jsonl") result
    let rows ← readLines (output / s!"{variant}.jsonl")
    let start ← IO.monoNanosNow
    let summary ← inspectMatrix "compilatrix" rows
    checkerRegressions "compilatrix" rows
    let checkNs := (← IO.monoNanosNow) - start
    let identity ← field summary "matrix_blake3"
    if let some expected := matrixIdentity then need (identity == expected) "paired complete arena observations differ"
    matrixIdentity := some identity
    summaries := summaries.push (Json.mkObj [("variant", toJson variant), ("result", summary), ("independent_check_ns", toJson checkNs)])
    IO.println s!"counter-fold verify: {variant}, 585 inputs and 19305 complete arena observations"
  let mut negatives := #[]
  for (name, bytes, reason) in [
      ("magic", datasetBytes.set! 0 0, "wrong binary magic"),
      ("count", datasetBytes.set! 8 0, "wrong dataset inventory"),
      ("metadata", datasetBytes.set! 16 1, "noncanonical dataset metadata"),
      ("padding", datasetBytes.set! 48 1, "nonzero dataset padding"),
      ("trailing", datasetBytes.push 0, "trailing binary input"),
      ("truncated", datasetBytes.extract 0 (datasetBytes.size - 1), "truncated binary input")] do
    let path := output / s!"bad-{name}.bin"
    IO.FS.writeBinFile path bytes
    for variant in variants do
      let result ← IO.Process.output {
        cmd := (build / s!"bin/{variant}").toString,
        args := #["compilatrix", "verify", path.toString], env := runtimeEnv }
      need (result.exitCode != 0 && result.stderr.contains reason) s!"{variant} accepted malformed dataset {name}"
      negatives := negatives.push (Json.mkObj [("variant", toJson variant), ("case", toJson name),
        ("exit_code", toJson result.exitCode.toNat), ("stderr", toJson result.stderr)])
  let _ ← inspectBuild build
  writeJson (output / "correctness.json") (Json.mkObj [("format", toJson "compilatrix/counter-fold-correctness/1"),
    ("build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))),
    ("executables", ← field metadata "executables"), ("matrices", Json.arr summaries),
    ("malformed_datasets", Json.arr negatives), ("status", toJson "passed")])

def smokeSuite (build output : FilePath) (core : Nat) : IO Unit := do
  let build ← absolute build
  fresh output
  let metadata ← inspectBuild build
  let schedule : Schedule := {
    mode := 0, samples := 1, warmNs := 10000000,
    order := (List.range 38).toArray, operations := Array.replicate 38 (chunkSize * 6) }
  let mut samples := #[]
  for variant in variants do
    let rows ← runScheduled build (output / s!"{variant}.jsonl") variant schedule core
    samples := samples ++ rows
  need (samples.size == 76) "counter-fold smoke inventory disagrees"
  let first ← readLines (output / "baseline.jsonl")
  rejects "missing paired sample" "run inventory" (inspectRun "compilatrix" schedule (first.pop) *> pure ())
  for (key, value, reason) in [("operations", toJson (1 : Nat), "sample identity"),
      ("sink", toJson (0 : Nat), "timed sink"), ("elapsed_ns", toJson (0 : Nat), "timer/chunk")] do
    rejects key reason (inspectSample "compilatrix" 0 0 0 (chunkSize * 6) (← replaceAt samples[0]! [key] value))
  writeJson (output / "smoke.json") (Json.mkObj [("format", toJson "compilatrix/counter-fold-smoke/1"),
    ("executables", ← field metadata "executables"), ("samples", toJson samples), ("status", toJson "passed")])
  IO.println "counter-fold smoke: both executables, 76 timing rows, full results and sample corruption checks passed"

end Benchmarks.Compiler.CounterFold
