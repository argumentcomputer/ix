import Benchmarks.Compiler.Environment

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def minimumNs : Nat := 100000000
def pilotTargetNs : Nat := 200000000
def orderSeed : UInt64 := 1210345809
def blockCount : Nat := 30
def sessionCount : Nat := 3

def roundOperations (count : Nat) : Nat :=
  ((count + chunkSize * 6 - 1) / (chunkSize * 6)) * (chunkSize * 6)

def requireCorrectness (build correctness : FilePath) : IO Unit := do
  let result ← readJson (correctness / "correctness.json")
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  need ((← strField result "status") == "passed" && (← strField result "build_blake3") ==
    buildHash) "correctness record does not match the timed build"
  need ((← field result "executables") == (← field (← inspectBuild build) "executables")) "correctness executable identities differ"

def runUpstream (build output : FilePath) (name : String) (value operations samples core : Nat)
    (measurement : Bool := false) : IO (Array Json) := do
  let result ← streamed { cmd := "taskset", args := #["--cpu-list", toString core,
    (build / "bin/worker-launcher").toString,
    (build / s!"bin/upstream-{name}").toString, toString operations, toString samples] } output
  IO.FS.writeFile (output.withExtension "stderr") result.stderr
  need (result.exitCode == 0) s!"upstream {name} timing failed: {result.stderr}"
  let rows ← readLines output
  need (rows.size == samples + 1 && (← kind rows[0]!) == "warmup" &&
    (← number rows[0]! "elapsed_ns") >= 1000000000) "upstream warm-up or sample inventory disagrees"
  for i in [:samples] do
    let row := rows[i + 1]!
    need ((← kind row) == "sample" && (← number row "sample") == i &&
      (← number row "operations") == operations && (← number row "sink") == value * operations &&
      (← number row "elapsed_ns") > 0) "upstream timed sample identity or result disagrees"
    if measurement then need ((← number row "elapsed_ns") >= minimumNs) "upstream measured sample shorter than 100 ms"
  return rows.extract 1 rows.size

def pilotSuite (build correctness output : FilePath) (core : Nat) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  requireCorrectness build correctness
  fresh output
  let before ← environment core
  writeJson (output / "environment-start.json") before
  environmentRegressions before
  let initial : Schedule := {
    mode := 1, samples := 1, warmNs := 1000000000,
    order := (List.range 38).toArray, operations := Array.replicate 38 (chunkSize * 6) }
  let mut counts := initial.operations
  let mut estimates : Array Json := #[]
  for implementation in implementations do
    let samples ← runScheduled build (output / s!"initial-{implementation}.jsonl") implementation initial core
    for row in samples do
      let id ← number row "row"
      let operations ← number row "operations"
      let elapsed ← number row "elapsed_ns"
      let count := roundOperations ((operations * pilotTargetNs + elapsed - 1) / elapsed)
      counts := counts.set! id (max counts[id]! count)
      estimates := estimates.push (Json.mkObj [("implementation", toJson implementation), ("row", toJson id),
        ("elapsed_ns", toJson elapsed), ("operations", toJson operations), ("envelope_ns", ← field row "envelope_ns")])
    IO.println s!"benchmark pilot: initial {implementation} complete"
  let schedule := { initial with operations := counts }
  let mut confirmation := #[]
  for implementation in implementations do
    let samples ← runScheduled build (output / s!"confirmation-{implementation}.jsonl") implementation schedule core
    for row in samples do
      need ((← number row "elapsed_ns") >= minimumNs) s!"pilot count needs a new premeasurement calibration: {implementation}"
      let id ← number row "row"
      confirmation := confirmation.push (Json.mkObj [("implementation", toJson implementation), ("row", toJson id),
        ("elapsed_ns", ← field row "elapsed_ns"), ("envelope_ns", ← field row "envelope_ns")])
    IO.println s!"benchmark pilot: confirmed {implementation}"
  let mut upstream := #[]
  for (name, value) in [("applyClosed", 3), ("letClosed", 4)] do
    let samples ← runUpstream build (output / s!"initial-upstream-{name}.jsonl") name value 1000000 1 core
    let elapsed ← number samples[0]! "elapsed_ns"
    let operations := roundOperations ((1000000 * pilotTargetNs + elapsed - 1) / elapsed)
    let _ ← runUpstream build (output / s!"confirmation-upstream-{name}.jsonl") name value operations 1 core true
    upstream := upstream.push (Json.mkObj [("name", toJson name), ("value", toJson value), ("operations", toJson operations)])
  let after ← environment core
  writeJson (output / "environment-end.json") after
  need (← stableEnvironment before after) "pilot environment drifted; no schedule frozen"
  let _ ← inspectBuild build
  let mut state := orderSeed
  let mut blocks := #[]
  for block in [:blockCount] do
    let (order, next) := shuffled (List.range 38).toArray state
    let (implementationOrder, next) := shuffled (List.range implementations.size).toArray next
    state := next
    let schedule : Schedule := { mode := 2, samples := 3, warmNs := 1000000000, order, operations := counts }
    blocks := blocks.push (Json.mkObj [("block", toJson block), ("session", toJson (block / 10)),
      ("implementation_order", toJson (implementationOrder.map (implementations[·]!))), ("schedule", toJson schedule)])
  writeJson (output / "freeze.json") (Json.mkObj [
    ("format", toJson "compilatrix/benchmark-freeze/1"), ("build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))) ,
    ("environment", before), ("core", toJson core), ("pilot_target_ns", toJson pilotTargetNs),
    ("minimum_sample_ns", toJson minimumNs), ("resource_bound_rss_kb", toJson (2097152 : Nat)),
    ("timer_chunk_minimum_factor", toJson (100 : Nat)), ("session_separation_seconds", toJson (60 : Nat)),
    ("order_seed", toJson orderSeed.toNat), ("blocks", Json.arr blocks), ("upstream", Json.arr upstream),
    ("initial_estimates", Json.arr estimates), ("confirmation", Json.arr confirmation),
    ("invalidations", toJson (["changed boot, CPU identity/topology, kernel, affinity, governor/turbo, clocksource, or declared runtime environment",
      "incorrect sink/schema, executable drift, process failure, RSS above 2 GiB, sample below 100 ms, chunk below 100 minimum clock-pair costs",
      "slow samples, context switches, page faults, load, and frequency variation are retained and reported"] : List String)),
    ("bootstrap", toJson "hierarchical paired bootstrap: resample three sessions, then ten whole paired blocks within each selected session"),
    ("bootstrap_replicates", toJson (10000 : Nat)), ("bootstrap_seed", toJson (2671931027 : Nat))])
  IO.println s!"benchmark pilot: fixed common counts, 30 randomized paired blocks, and two upstream entries frozen in {output}"

end Benchmarks.Compiler
