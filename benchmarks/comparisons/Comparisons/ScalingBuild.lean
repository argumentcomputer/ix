import Comparisons.ScalingPlan

namespace Benchmark.CompilerScaling
open Lean System Compilatrix.Tools.Check Compilatrix.Tools.UniqueCheck

def buildSuite (output : FilePath) (profile : String) (worker : FilePath)
    (gcc : String := "gcc") (timer : String := "time") : IO Unit := do
  need (["smoke", "full"].contains profile) "scaling profile must be smoke or full"
  let output ← absolute output
  let worker ← absolute worker
  let cwd ← IO.currentDir
  need (!output.toString.startsWith (cwd.toString ++ "/") ||
    output.toString.startsWith ((cwd / "benchmarks/runs").toString ++ "/"))
    "put scaling bundles outside the source tree or under ignored benchmarks/runs"
  fresh output
  for name in ["inputs", "artifacts", "tools", "harness", "logs"] do IO.FS.createDirAll (output / name)
  let core ← firstCore
  writeJson (output / "environment.json") (← environment core)
  IO.FS.writeFile (output / "protocol.md") (← IO.FS.readFile "benchmarks/compiler-scaling.md")
  let _ ← run "cp" #[worker.toString, (output / "tools/compiler-scaling").toString]
  let _ ← run "cp" #[(← IO.appPath).toString, (output / "tools/benchmark").toString]
  IO.FS.writeFile (output / "harness/scaling_harness.c") (← IO.FS.readFile "benchmarks/native/scaling_harness.c")
  let _ ← logged (output / "logs") "harness" gcc
    (cFlags ++ #["-Wall", "-Wextra", "-Werror", "-c", (output / "harness/scaling_harness.c").toString,
      "-o", (output / "harness/driver.o").toString]) #[] none timer
  let mut tools := #[]
  let mut roots : Array String := #[]
  for (name, command) in [("gcc", gcc), ("lean", "lean"), ("lake", "lake"), ("time", timer),
      ("taskset", "taskset"), ("prlimit", "prlimit"), ("timeout", "timeout")] do
    let path := (← run "which" #[command]).trimAscii.toString
    let resolved := (← run "readlink" #["-f", path]).trimAscii.toString
    let version ← run command #["--version"]
    tools := tools.push (Json.mkObj [("name", toJson name), ("resolved", toJson resolved),
      ("blake3", toJson (digest (← IO.FS.readBinFile resolved))), ("version", toJson version)])
    if resolved.startsWith "/nix/store/" then
      let root := String.intercalate "/" ((resolved.splitOn "/").take 4)
      if !roots.contains root then roots := roots.push root
  writeJson (output / "tool-identities.json") (Json.arr tools)
  let closure ← IO.Process.output { cmd := "nix-store", args := #["--query", "--requisites"] ++ roots }
  IO.FS.writeFile (output / "nix-closure.txt") closure.stdout
  writeJson (output / "nix-closure-status.json") (Json.mkObj [("roots", toJson roots), ("exit_code", toJson closure.exitCode.toNat), ("stderr", toJson closure.stderr)])
  let mut rows := #[]
  let mut pairs := #[]
  for case in cases profile do
    let input := output / "inputs" / s!"{case.id}.json"
    runWorker (output / "tools/compiler-scaling") (output / "logs") s!"generate-{case.id}"
      #["generate", case.family, toString case.size, if case.edited then "1" else "0", input.toString] core timer
    let coldMode := if case.edited then "edit-cold" else "cold"
    let coldId := s!"{case.id}-{coldMode}"
    let cold := output / "artifacts" / coldId
    runWorker (output / "tools/compiler-scaling") (output / "logs") coldId #["compile", input.toString, cold.toString] core timer
    let coldReference ← reference cold
    rows := rows.push (Json.mkObj [("id", toJson coldId), ("case", toJson case), ("mode", toJson coldMode),
      ("input", toJson s!"inputs/{case.id}.json"), ("cache", Json.null), ("reference", coldReference)])
    if ← (cold / "hpt.store").pathExists then
      let baseId := s!"{case.family}-{case.size}-cold"
      let cacheId := if case.edited then baseId else coldId
      let cache := s!"artifacts/{cacheId}/hpt.store"
      let warmMode := if case.edited then "edit-warm" else "warm"
      let warmId := s!"{case.id}-{warmMode}"
      let warm := output / "artifacts" / warmId
      runWorker (output / "tools/compiler-scaling") (output / "logs") warmId
        #["compile", input.toString, warm.toString, (output / cache).toString] core timer
      let warmReference ← reference warm
      let prior ← if case.edited then do
          let base ← present (← rows.findM? fun row => return (← strField row "id") == baseId) "dependency edit has no baseline cache"
          pure (some (← field (← field base "reference") "outcome"))
        else pure none
      let reuse ← cachePair coldReference warmReference prior
      pairs := pairs.push (Json.mkObj [("cold", toJson coldId), ("warm", toJson warmId), ("reuse", reuse)])
      rows := rows.push (Json.mkObj [("id", toJson warmId), ("case", toJson case), ("mode", toJson warmMode),
        ("input", toJson s!"inputs/{case.id}.json"), ("cache", toJson cache), ("reference", warmReference)])
    IO.println s!"compiler scaling build: {case.id}"
  writeJson (output / "build.json") (Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-build/1"), ("profile", toJson profile), ("cases", toJson (cases profile)),
    ("rows", Json.arr rows), ("cache_pairs", Json.arr pairs), ("gcc", toJson gcc), ("timer_tool", toJson timer),
    ("core", toJson core), ("worker_overrides", toJson workerEnv),
    ("build_environment", toJson (← buildEnvNames.mapM fun name => do return (name, ← IO.getEnv name))),
    ("inputs", ← recordFiles (output / "inputs")), ("tools", ← recordFiles (output / "tools")),
    ("harness", ← recordFiles (output / "harness")),
    ("protocol_blake3", toJson (digest (← IO.FS.readBinFile (output / "protocol.md")))),
    ("tool_identities_blake3", toJson (digest (← IO.FS.readBinFile (output / "tool-identities.json"))))])
  let _ ← inspectBuild output
  let _ ← sourceSnapshot output
  IO.println s!"compiler scaling build: {rows.size} rows; canonical inputs, evidence and compiler seeds retained in {output}"

def golden (metadata : Json) : IO Json := do
  let rows ← arrField metadata "rows"
  let mut results := #[]
  for case in cases "smoke" do
    let mode := if case.edited then "edit-cold" else "cold"
    let id := s!"{case.id}-{mode}"
    let row ← present (← rows.findM? fun row => return (← strField row "id") == id) "missing golden workload"
    let reference ← field row "reference"
    let outcome ← field reference "outcome"
    let selected := (← pairs outcome).filter fun (key, _) =>
      ["family", "size", "edited", "status", "rejection", "source_work", "source_coverage_entries", "ixir1_declarations", "ixir1_bytes",
        "hpt_store_bytes", "hpt_certificate_artifacts", "ixir2_stats", "ixir2_shape", "snapshot_bytes", "requested_endpoint",
        "native_interfaces", "native_allocation_bound", "x86_blocks", "x86_instructions", "x86_text_bytes", "elf_bytes"].contains key
    results := results.push (Json.mkObj [("id", toJson id), ("outcome", Json.mkObj selected),
      ("artifacts_blake3", toJson (digest (← field reference "artifacts").compress.toUTF8))])
  return Json.mkObj [("format", toJson "compilatrix/compiler-scaling-golden/1"), ("cases", Json.arr results)]

def regressions (build output : FilePath) (metadata : Json) : IO Unit := do
  let rows ← arrField metadata "rows"
  let first := rows[0]!
  let directory := build / "artifacts" / (← strField first "id")
  let reference ← field first "reference"
  let metrics ← readJson (directory / "measurements.json")
  let stages ← arrField metrics "stages"
  rejects "duplicate phase" "duplicate compiler stage" (stageIdentities (← replaceAt metrics ["stages"] (Json.arr (stages.push stages[0]!))) *> pure ())
  let zero ← replaceAt stages[0]! ["elapsed_ns"] (toJson (0 : Nat))
  rejects "zero duration" "zero compiler stage" (stageIdentities (← replaceAt metrics ["stages"] (Json.arr (stages.set! 0 zero))) *> pure ())
  let missing ← replaceAt reference ["stages"] (Json.arr (← arrField reference "stages").pop)
  rejects "missing phase" "compiler stage inventory" (artifactCheck directory missing)
  for (name, key, value) in [("source-root", "root", toJson (String.ofList (List.replicate 64 '0'))),
      ("compiler-policy", "policy", Json.null)] do
    let input ← readJson (directory / "input.json")
    let corrupted ← replaceAt input ["source", key] value
    let path := output / s!"{name}.json"
    writeJson path corrupted
    let result ← IO.Process.output {
      cmd := (build / "tools/compiler-scaling").toString
      args := #["compile", path.toString, (output / s!"{name}-out").toString], env := workerEnv }
    need (result.exitCode != 0 && result.stderr.contains "source bytes or fixed compiler policy") "changed source input was not rejected"
    IO.FS.writeFile (output / s!"{name}.stderr") result.stderr
  for (name, file) in [("snapshot", "ixir2.bin"), ("elf", "main.o"), ("hpt", "hpt.store")] do
    let corrupted := output / s!"bad-{name}"
    let _ ← run "cp" #["-R", directory.toString, corrupted.toString]
    let path := corrupted / file
    let bytes ← IO.FS.readBinFile path
    IO.FS.writeBinFile path (if name == "snapshot" then bytes.push 0 else bytes.set! 0 (bytes[0]! ^^^ 1))
    let result ← IO.Process.output {
      cmd := (build / "tools/compiler-scaling").toString
      args := #["verify", corrupted.toString, (output / s!"bad-{name}-verified.json").toString], env := workerEnv }
    let reason := if name == "snapshot" then "trailing" else if name == "elf" then "retained ELF differs" else "retained HPT evidence differs"
    need (result.exitCode != 0 && result.stderr.contains reason) s!"corrupted {name} escaped its checker"
    IO.FS.writeFile (output / s!"bad-{name}.stderr") result.stderr
  writeJson (output / "regressions.json") (Json.mkObj [("status", toJson "passed"), ("cases", toJson (8 : Nat))])

def verifySuite (build output : FilePath) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  fresh output
  for name in ["logs", "native", "regressions"] do IO.FS.createDirAll (output / name)
  let metadata ← inspectBuild build
  need ((← golden metadata) == (← readJson "fixtures/compiler-scaling/expected.json")) "compiler scaling differs from the reviewed golden"
  let rows ← arrField metadata "rows"
  let core ← number metadata "core"
  let timer ← strField metadata "timer_tool"
  let gcc ← strField metadata "gcc"
  let mut results := #[]
  for row in rows do
    let mode ← strField row "mode"
    if mode == "warm" || mode == "edit-warm" then continue
    let id ← strField row "id"
    let directory := build / "artifacts" / id
    let checkedPath := output / s!"{id}.json"
    runWorker (build / "tools/compiler-scaling") (output / "logs") s!"verify-{id}"
      #["verify", directory.toString, checkedPath.toString] core timer
    let mut native := Json.null
    let outcome ← field (← field row "reference") "outcome"
    if (← strField outcome "status") == "compiled" then
      let executable := output / "native" / id
      let _ ← logged (output / "logs") s!"link-{id}" gcc
        (cFlags ++ #[(build / "harness/driver.o").toString, (directory / "main.o").toString,
          "-Wl,-z,noexecstack", "-o", executable.toString]) #[] none timer
      let case ← checked (fromJson? (← field row "case") : Except String Case)
      let raw ← logged (output / "logs") s!"native-{id}" "timeout"
        #["--kill-after=2s", "10s", executable.toString, case.family, toString case.size] #[] none timer
      native ← checked (Json.parse raw)
      let count := if ["call-depth", "allocations"].contains case.family then 34 else 33
      need (native == Json.mkObj [("calls", toJson count), ("values", toJson true), ("saved_registers", toJson true),
        ("finite_workspace", toJson true), ("exact_counters", toJson true), ("reclaimed", toJson true), ("capacity_rejected", toJson true)])
        "independent native harness result disagrees"
    results := results.push (Json.mkObj [("id", toJson id), ("compiler_replay", ← readJson checkedPath), ("native", native)])
    IO.println s!"compiler scaling verify: {id}"
  regressions build (output / "regressions") metadata
  writeJson (output / "correctness.json") (Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-correctness/1"), ("status", toJson "passed"),
    ("build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))),
    ("cases", Json.arr results), ("cache_pairs", ← field metadata "cache_pairs"), ("regressions", toJson (8 : Nat))])

end Benchmark.CompilerScaling
