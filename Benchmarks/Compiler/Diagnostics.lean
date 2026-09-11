import Benchmarks.Compiler.Analyze

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def collectionDiagnostic (build output : FilePath) (core : Nat) (schedule : Schedule)
    (measurement : Bool) : IO Json := do
  let path := output / "cakeml-gc.jsonl"
  writeSchedule (path.withExtension "bin") schedule
  let result ← streamed { cmd := "taskset", args := #["--cpu-list", toString core,
    (build / "bin/worker-launcher").toString,
    (build / "bin/cakeml-diagnostic").toString, "cakeml", "run", (build / "datasets/datasets.bin").toString,
    (path.withExtension "bin").toString], env := runtimeEnv } path
  IO.FS.writeFile (path.withExtension "stderr") result.stderr
  need (result.exitCode == 0) "CakeML collection diagnostic failed"
  let rows ← readLines path
  let mut nativeRows := #[]
  let mut collectionRows := #[]
  let mut terminal : Option Json := none
  for row in rows do
    match ← kind row with
    | "gc-sample" => collectionRows := collectionRows.push row
    | "terminal-gc" =>
      need terminal.isNone "duplicate terminal collection record"
      terminal := some row
    | _ => nativeRows := nativeRows.push row
  let samples ← inspectRun "cakeml" schedule nativeRows measurement
  need (collectionRows.size == schedule.order.size * schedule.samples) "incomplete collection diagnostic"
  let mut collections := 0
  let mut lastTotal := 0
  let mut maximumLive := 0
  let mut liveValues : Array Nat := #[]
  let mut maxRss := 0
  for i in [:collectionRows.size] do
    let row := collectionRows[i]!
    need ((← number row "row") == (← number samples[i]! "row") &&
      (← number row "sample") == (← number samples[i]! "sample")) "collection diagnostic sample identity disagrees"
    let count ← number row "collections"
    let total ← number row "total_collections"
    need (count > 0 && total >= lastTotal + count) "lifecycle diagnostic did not exercise natural collection cycles"
    collections := collections + count
    lastTotal := total
    let live ← number row "last_post_gc_live_bytes"
    need (live < 8388608) "post-collection retention exceeded the frozen diagnostic bound"
    liveValues := liveValues.push live
    maximumLive := max maximumLive live
    maxRss := max maxRss (← number samples[i]! "rss_kb")
  let terminalObservation ← present terminal "missing terminal collection observation"
  need ((← number terminalObservation "total_collections") == lastTotal + 1 &&
    (← number terminalObservation "post_gc_live_bytes") < 8388608) "terminal collection inventory or retention disagrees"
  return Json.mkObj [("schedule", toJson schedule), ("natural_collections_in_sample_envelopes", toJson collections),
    ("maximum_post_gc_live_bytes", toJson maximumLive), ("post_gc_live_bytes_across_samples", toJson liveValues),
    ("maximum_current_rss_kb", toJson maxRss), ("terminal_collection", terminalObservation),
    ("sample_envelopes", Json.arr collectionRows), ("raw_blake3", toJson (digest (← IO.FS.readBinFile path))),
    ("interpretation", toJson "separate instrumented lifecycle executions; GC time uses the pinned runtime gettimeofday hook; terminal elapsed time uses CLOCK_MONOTONIC_RAW")]

def gcSmokeSuite (build output : FilePath) (core : Nat) : IO Unit := do
  let build ← absolute build
  fresh output
  let _ ← inspectBuild build
  let schedule : Schedule := {
    mode := 0, samples := 1, warmNs := 10000000, order := #[28, 31, 34, 37],
    operations := Array.replicate 38 (chunkSize * 6) }
  let gc ← collectionDiagnostic build output core schedule false
  writeJson (output / "gc-smoke.json") (Json.mkObj [("format", toJson "compilatrix/benchmark-gc-smoke/1"),
    ("build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))) ,
    ("gc", gc), ("status", toJson "passed")])
  IO.println "benchmark GC smoke: all four lifecycle domains exercise natural collections, bounded retention, and one actual terminal collection"

def diagnoseSuite (build pilot output : FilePath) (core : Nat) : IO Unit := do
  fresh output
  let freeze ← inspectFreeze build pilot
  need (core == (← number freeze "core")) "diagnostic core differs from frozen run"
  let first := (← arrField freeze "blocks")[0]!
  let common ← checked (fromJson? (← field first "schedule") : Except String Schedule)
  let schedule : Schedule := {
    mode := 1, samples := 5, warmNs := 1000000000, order := #[28, 31, 34, 37], operations := common.operations }
  let gc ← collectionDiagnostic build output core schedule true
  let mut compilerCosts := #[]
  for name in ["compilatrix-produce", "compilatrix-independent-gate", "lean-generate-c", "lean-kernel",
      "cakeml-kernel", "kernel-compcert", "kernel-gcc", "kernel-clang",
      "upstream-applyClosed-produce", "upstream-applyClosed-check", "upstream-letClosed-produce", "upstream-letClosed-check"] do
    compilerCosts := compilerCosts.push (Json.mkObj [("name", toJson name),
      ("resources", ← readJson (build / s!"diagnostics/build/{name}.resources.json")),
      ("command", ← readJson (build / s!"diagnostics/build/{name}.command.json"))])
  let mut sizes := #[]
  for name in ["compilatrix-main", "compilatrix-release", "lean-kernel", "cakeml-kernel", "compcert-kernel", "gcc-kernel", "clang-kernel",
      "compilatrix", "lean", "cakeml", "compcert", "gcc", "clang"] do
    sizes := sizes.push (Json.mkObj [("name", toJson name),
      ("gnu_size_A", toJson (← IO.FS.readFile (build / s!"diagnostics/build/size-{name}.stdout")))])
  let mut upstream := #[]
  for name in ["applyClosed", "letClosed"] do
    let directory := build / s!"artifacts/upstream-{name}"
    let snapshot ← readJson (directory / s!"upstream-{name}.json")
    let native ← field snapshot "native"
    let row := (← arrField (← readJson (directory / "report.json")) "cases")[0]!
    let compilation ← field snapshot "compilation"
    let mut encoded := #[]
    for (label, container, key, payload) in [("ixir0_declarations", ← field compilation "ixir0", "declarations", "preimage"),
        ("ixir1_artifacts", ← field compilation "ixir1", "artifacts", "preimage"),
        ("hpt_certificates", ← field compilation "hpt", "artifacts", "bytes")] do
      let artifacts ← arrField container key
      let mut total := 0
      for artifact in artifacts do total := total + (← byteField artifact payload).size
      encoded := encoded.push (Json.mkObj [("name", toJson label), ("count", toJson artifacts.size), ("encoded_bytes", toJson total)])
    let mut pieces := #[]
    for key in ["input", "compilation", "observations", "native"] do
      let json ← field snapshot key
      pieces := pieces.push (Json.mkObj [("name", toJson key), ("canonical_json_bytes", toJson json.compress.toUTF8.size)])
    upstream := upstream.push (Json.mkObj [("name", toJson name), ("root", ← field row "root"),
      ("source_constants", ← field row "source_constants"), ("source_piece_bytes", toJson (if name == "applyClosed" then 662 else 670 : Nat)),
      ("snapshot_bytes", toJson (← IO.FS.readBinFile (directory / s!"upstream-{name}.json")).size),
      ("snapshot_parts", Json.arr pieces), ("encoded_artifacts", Json.arr encoded),
      ("text_bytes", ← field native "text_bytes"), ("object_bytes", ← field native "object_bytes"),
      ("baseline_counters", ← field row "observation"), ("native_heap", ← field native "native_heap"),
      ("scope", toJson "serialized artifacts and executable certificates; Lean proof-term allocation is not inferred from JSON size")])
  let hardware ← try
      let which ← IO.Process.output { cmd := "which", args := #["perf"] }
      if which.exitCode != 0 then pure (Json.mkObj [("status", toJson "unavailable"), ("reason", toJson "perf is not installed in the recorded runtime environment")])
      else do
        let perf ← IO.Process.output {
          cmd := which.stdout.trimAscii.toString,
          args := #["stat", "-x,", "-e", "cycles,instructions,branches,branch-misses,cache-misses,page-faults",
            "--", "taskset", "--cpu-list", toString core, (build / "bin/upstream-applyClosed").toString, "1000000", "1"] }
        IO.FS.writeFile (output / "perf.stdout") perf.stdout
        IO.FS.writeFile (output / "perf.stderr") perf.stderr
        pure (Json.mkObj [("status", toJson (if perf.exitCode == 0 then "available-diagnostic-only" else "unavailable")),
          ("exit_code", toJson perf.exitCode.toNat), ("scope", toJson "whole upstream applyClosed diagnostic process including warmup and checks"),
          ("raw_events_and_scaling", toJson perf.stderr)])
    catch error => pure (Json.mkObj [("status", toJson "unavailable"), ("reason", toJson error.toString)])
  let _ ← inspectBuild build
  writeJson (output / "diagnostics.json") (Json.mkObj [("format", toJson "compilatrix/benchmark-diagnostics/1"),
    ("build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))),
    ("gc", gc),
    ("hardware_counters", hardware), ("compiler_costs", Json.arr compilerCosts), ("code_sizes", Json.arr sizes),
    ("upstream_artifact_growth", Json.arr upstream), ("status", toJson "passed")])
  IO.println s!"benchmark diagnostics: {← number gc "natural_collections_in_sample_envelopes"} natural GC cycles, bounded post-collection storage, separate terminal GC, compiler costs and sizes retained"

end Benchmarks.Compiler
