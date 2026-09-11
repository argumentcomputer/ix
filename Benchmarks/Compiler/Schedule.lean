import Benchmarks.Compiler.Verify

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

structure Schedule where
  mode : Nat
  samples : Nat
  warmNs : Nat
  order : Array Nat
  operations : Array Nat
  deriving ToJson, FromJson, BEq

def Schedule.valid (schedule : Schedule) : Bool :=
  schedule.mode ≤ 2 && 0 < schedule.samples && schedule.samples ≤ 10 && schedule.warmNs ≤ 10000000000 &&
  0 < schedule.order.size && schedule.order.size ≤ 38 && schedule.order.toList.Nodup &&
  schedule.order.all (· < 38) && schedule.operations.size == 38 &&
  schedule.operations.all (fun count => 0 < count && count ≤ 1000000000000 && count % (chunkSize * 6) == 0) &&
  (schedule.mode != 2 || (schedule.order.size == 38 && schedule.samples == 3 && schedule.warmNs ≥ 1000000000))

def Schedule.bytes (schedule : Schedule) : ByteArray := Id.run do
  let mut bytes := scheduleMagic.toUTF8
  for value in [schedule.order.size, schedule.samples, schedule.warmNs, chunkSize, schedule.mode] do
    bytes := bytes ++ wordBytes value.toUInt64
  for id in schedule.order do
    let row := timingCases[id]!
    for value in [id, row.length, row.domain, row.profile, schedule.operations[id]!] do
      bytes := bytes ++ wordBytes value.toUInt64
  return bytes

def writeSchedule (path : FilePath) (schedule : Schedule) : IO Unit := do
  need schedule.valid "invalid benchmark schedule"
  IO.FS.writeBinFile path schedule.bytes

def shuffled (values : Array Nat) (seed : UInt64) : Array Nat × UInt64 := Id.run do
  let mut values := values
  let mut state := seed
  for index in [:values.size] do
    state := nextRandom state
    let target := index + (state.toNat % (values.size - index))
    values := values.swapIfInBounds index target
  return (values, state)

def inspectRun (implementation : String) (schedule : Schedule) (rows : Array Json)
    (measurement : Bool := false) : IO (Array Json) := do
  need schedule.valid "invalid benchmark schedule"
  need (rows.size == 4 + schedule.order.size * schedule.samples) "benchmark run inventory disagrees"
  inspectMetadata implementation rows[0]!
  inspectControl rows[1]!
  let warm := rows[2]!
  need ((← kind warm) == "warmup" && (← number warm "elapsed_ns") >= schedule.warmNs &&
    (← number warm "operations") > 0 && (← number warm "operations") % chunkSize == 0) "benchmark warm-up incomplete"
  need ((← number warm "sink") == (sampleSink timingCases[28]! (← number warm "operations")).toNat) "benchmark warm-up sink disagrees"
  let timerPair ← number rows[0]! "timer_pair_min_ns"
  let mut index := 3
  let mut samples := #[]
  for id in schedule.order do
    for sample in [:schedule.samples] do
      let row := rows[index]!
      inspectSample implementation schedule.mode id sample schedule.operations[id]! row
      if measurement then
        need ((← number row "elapsed_ns") >= 100000000) "measured sample shorter than 100 ms"
        need ((← number row "minimum_chunk_ns") >= 100 * timerPair) "timed chunk does not dominate timer overhead"
      samples := samples.push row
      index := index + 1
  need ((← kind rows[index]!) == "completed" && (← number rows[index]! "rows") == schedule.order.size &&
    (← number rows[index]! "samples_per_row") == schedule.samples) "benchmark run did not complete"
  return samples

def runScheduled (build output : FilePath) (implementation : String) (schedule : Schedule)
    (core : Nat) : IO (Array Json) := do
  let schedulePath := output.withExtension "bin"
  writeSchedule schedulePath schedule
  -- All compilation has finished before this function is used for measurement.
  let result ← streamed {
    cmd := "taskset"
    args := #["--cpu-list", toString core, (build / "bin/worker-launcher").toString,
      (build / s!"bin/{implementation}").toString, implementation,
      "run", (build / "datasets/datasets.bin").toString, schedulePath.toString]
    env := runtimeEnv } output
  IO.FS.writeFile (output.withExtension "stderr") result.stderr
  writeJson (output.withExtension "process.json") (Json.mkObj [("exit_code", toJson result.exitCode.toNat),
    ("implementation", toJson implementation), ("core", toJson core), ("schedule", toJson schedule),
    ("schedule_blake3", toJson (digest schedule.bytes)), ("stdout_blake3", toJson (digest result.stdout.toUTF8))])
  need (result.exitCode == 0) s!"benchmark {implementation} failed: {result.stderr}"
  inspectRun implementation schedule (← readLines output) (schedule.mode == 2)

def smokeSuite (build output : FilePath) (core : Nat) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  fresh output
  let metadata ← inspectBuild build
  let schedule : Schedule := {
    mode := 0, samples := 1, warmNs := 10000000,
    order := (List.range 38).toArray, operations := Array.replicate 38 (chunkSize * 6) }
  let mut samples := #[]
  for implementation in implementations do
    let rows ← runScheduled build (output / s!"{implementation}.jsonl") implementation schedule core
    samples := samples ++ rows
    IO.println s!"benchmark smoke: {implementation}, {rows.size} timing rows and periodic full checks"
  need (samples.size == 228) "smoke run incomplete"
  let sample := samples[0]!
  for (name, path, replacement, fragment) in [
      ("mode", ["mode"], toJson (2 : Nat), "sample identity"),
      ("profile id", ["row"], toJson (19 : Nat), "sample identity"),
      ("implementation", ["implementation"], toJson "clang", "sample identity"),
      ("operation count", ["operations"], toJson (1 : Nat), "sample identity"),
      ("sink", ["sink"], toJson (0 : Nat), "timed sink"),
      ("timer calls", ["timer_calls"], toJson (1 : Nat), "timer/chunk"),
      ("zero time", ["elapsed_ns"], toJson (0 : Nat), "timer/chunk")] do
    rejects name fragment (inspectSample "compilatrix" 0 0 0 (chunkSize * 6) (← replaceAt sample path replacement))
  let first ← readLines (output / "compilatrix.jsonl")
  rejects "missing samples" "run inventory" (inspectRun "compilatrix" schedule (first.extract 0 (first.size - 1)) *> pure ())
  rejects "mixed samples" "sample identity" (inspectRun "gcc" schedule (first.set! 0 (← readLines (output / "gcc.jsonl"))[0]!) *> pure ())
  let canonical := schedule.bytes
  let badSchedules : Array (String × ByteArray × String) := #[
    ("magic", canonical.set! 0 0, "wrong binary magic"),
    ("empty", canonical.set! 8 0, "invalid schedule header"),
    ("samples", canonical.set! 16 0, "invalid schedule header"),
    ("chunk", canonical.set! 32 1, "invalid schedule header"),
    ("mode", canonical.set! 40 3, "invalid schedule header"),
    ("measurement-minimums", canonical.set! 40 2, "incomplete measurement schedule"),
    ("row-id", canonical.set! 48 38, "schedule row id out of range"),
    ("row-length", canonical.set! 56 1, "invalid schedule row"),
    ("operations", canonical.set! 80 1, "invalid schedule row"),
    ("duplicate", canonical.extract 0 88 ++ canonical.extract 48 88 ++ canonical.extract 128 canonical.size, "invalid schedule row"),
    ("truncated", canonical.extract 0 (canonical.size - 1), "truncated binary input"),
    ("trailing", canonical.push 0, "trailing binary input")]
  let mut negativeRows := #[]
  for (name, bytes, reason) in badSchedules do
    let path := output / s!"bad-schedule-{name}.bin"
    IO.FS.writeBinFile path bytes
    for implementation in implementations do
      let result ← IO.Process.output {
        cmd := (build / s!"bin/{implementation}").toString,
        args := #[implementation, "run", (build / "datasets/datasets.bin").toString, path.toString], env := runtimeEnv }
      need (result.exitCode != 0 && result.stderr.contains reason) s!"{implementation} accepted malformed schedule {name}"
      negativeRows := negativeRows.push (Json.mkObj [("implementation", toJson implementation), ("case", toJson name),
        ("exit_code", toJson result.exitCode.toNat), ("stderr", toJson result.stderr)])
  writeJson (output / "malformed-schedules.json") (Json.arr negativeRows)
  writeJson (output / "smoke.json") (Json.mkObj [("format", toJson "compilatrix/benchmark-smoke/1"),
    ("executables", ← field metadata "executables"), ("schedule", toJson schedule),
    ("samples", Json.arr samples), ("status", toJson "passed")])
  IO.println "benchmark smoke: six executables, 228 timing rows, periodic full results, and sample-schema corruptions passed"

end Benchmarks.Compiler
