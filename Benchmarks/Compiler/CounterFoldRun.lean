import Benchmarks.Compiler.CounterFoldBuild
import Benchmarks.Compiler.Analyze

namespace Benchmarks.Compiler.CounterFold
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def requireCorrectness (build correctness : FilePath) : IO Unit := do
  let result ← readJson (correctness / "correctness.json")
  let metadata ← inspectBuild build
  need ((← strField result "format") == "compilatrix/counter-fold-correctness/1" &&
    (← strField result "status") == "passed" && (← strField result "build_blake3") ==
    digest (← IO.FS.readBinFile (build / "build.json")) &&
    (← field result "executables") == (← field metadata "executables")) "counter-fold correctness identity disagrees"

def frozenBlocks (counts : Array Nat) : Array Json := Id.run do
  let mut state := orderSeed
  let mut blocks := #[]
  for block in [:blockCount] do
    let (order, next) := shuffled (List.range 38).toArray state
    let (variantOrder, next) := shuffled #[0, 1] next
    state := next
    let schedule : Schedule := { mode := 2, samples := 3, warmNs := 1000000000, order, operations := counts }
    blocks := blocks.push (Json.mkObj [("block", toJson block), ("session", toJson (block / 10)),
      ("variant_order", toJson (variantOrder.map (variants[·]!))), ("schedule", toJson schedule)])
  return blocks

def timingPolicy : Json := Json.mkObj [
  ("minimum_sample_ns", toJson minimumNs), ("pilot_target_ns", toJson pilotTargetNs),
  ("order_seed", toJson orderSeed.toNat), ("resource_bound_rss_kb", toJson (2097152 : Nat)),
  ("timer_chunk_minimum_factor", toJson (100 : Nat)), ("session_separation_seconds", toJson (60 : Nat)),
  ("bootstrap_replicates", toJson (10000 : Nat)), ("bootstrap_seed", toJson (2671931027 : Nat)),
  ("bootstrap", toJson "hierarchical paired bootstrap: resample three sessions, then ten whole paired blocks within each selected session")]

def inspectFreezeValue (buildHash : String) (freeze : Json) : IO Unit := do
  need ((← strField freeze "format") == "compilatrix/counter-fold-freeze/1" &&
    (← strField freeze "build_blake3") == buildHash &&
    (← field freeze "timing_policy") == timingPolicy) "counter-fold frozen identity or timing policy changed"
  let counts ← (← arrField freeze "operations").mapM nat
  let blocks ← arrField freeze "blocks"
  need (blocks == frozenBlocks counts) "counter-fold frozen randomized order changed"
  for block in blocks do
    let schedule ← checked (fromJson? (← field block "schedule") : Except String Schedule)
    need schedule.valid "counter-fold frozen schedule invalid"

def inspectFreeze (build pilot : FilePath) : IO Json := do
  let freeze ← readJson (pilot / "freeze.json")
  inspectFreezeValue (digest (← IO.FS.readBinFile (build / "build.json"))) freeze
  return freeze

def freezeRegressions (hash : String) (freeze : Json) : IO Unit := do
  for (name, path, value, reason) in [
      ("build", ["build_blake3"], toJson "different", "frozen identity"),
      ("floor", ["timing_policy", "minimum_sample_ns"], toJson (1 : Nat), "timing policy"),
      ("bootstrap", ["timing_policy", "bootstrap_seed"], toJson (1 : Nat), "timing policy"),
      ("missing block", ["blocks"], Json.arr #[], "randomized order")] do
    rejects name reason (inspectFreezeValue hash (← replaceAt freeze path value))
  let blocks ← arrField freeze "blocks"
  let changed ← replaceAt blocks[0]! ["variant_order"] (toJson #["baseline", "baseline"])
  rejects "duplicate variant" "randomized order"
    (inspectFreezeValue hash (← replaceAt freeze ["blocks"] (toJson (blocks.set! 0 changed))))

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
  let mut estimates := #[]
  for variant in variants do
    let samples ← runScheduled build (output / s!"initial-{variant}.jsonl") variant initial core
    for row in samples do
      let id ← number row "row"
      let operations ← number row "operations"
      let elapsed ← number row "elapsed_ns"
      counts := counts.set! id (max counts[id]! (roundOperations ((operations * pilotTargetNs + elapsed - 1) / elapsed)))
      estimates := estimates.push (Json.mkObj [("variant", toJson variant), ("observation", row)])
    IO.println s!"counter-fold pilot: initial {variant} complete"
  let schedule := { initial with operations := counts }
  let mut confirmation := #[]
  for variant in variants do
    let samples ← runScheduled build (output / s!"confirmation-{variant}.jsonl") variant schedule core
    for row in samples do
      need ((← number row "elapsed_ns") >= minimumNs) s!"new premeasurement calibration required: {variant}"
      confirmation := confirmation.push (Json.mkObj [("variant", toJson variant), ("observation", row)])
    IO.println s!"counter-fold pilot: confirmed {variant}"
  let after ← environment core
  writeJson (output / "environment-end.json") after
  need (← stableEnvironment before after) "counter-fold pilot environment drift"
  let _ ← inspectBuild build
  let hash := digest (← IO.FS.readBinFile (build / "build.json"))
  let freeze := Json.mkObj [("format", toJson "compilatrix/counter-fold-freeze/1"), ("build_blake3", toJson hash),
    ("environment", before), ("core", toJson core), ("timing_policy", timingPolicy), ("operations", toJson counts),
    ("blocks", toJson (frozenBlocks counts)), ("initial_estimates", toJson estimates), ("confirmation", toJson confirmation)]
  inspectFreezeValue hash freeze
  freezeRegressions hash freeze
  writeJson (output / "freeze.json") freeze
  IO.println "counter-fold pilot: common counts frozen for 30 paired blocks in three sessions"

def enriched (sample : Json) (variant : String) (block session order attempt : Nat)
    (buildHash freezeHash executableHash : String) : Json :=
  Json.mkObj [("variant", toJson variant),
    ("sample", Benchmarks.Compiler.enriched sample block session order attempt buildHash freezeHash executableHash)]

def measureSuite (build correctness pilot output : FilePath) (core : Nat) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  requireCorrectness build correctness
  let freeze ← inspectFreeze build pilot
  need ((← number freeze "core") == core) "counter-fold measurement core differs from pilot"
  let reference ← field freeze "environment"
  let initial ← environment core
  need (← stableEnvironment reference initial) "counter-fold measurement environment differs from pilot"
  fresh output
  for (source, name) in [(pilot, "freeze.json"), (correctness, "correctness.json")] do
    IO.FS.writeFile (output / name) (← IO.FS.readFile (source / name))
  writeJson (output / "environment-start.json") initial
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  let freezeHash := digest (← IO.FS.readBinFile (output / "freeze.json"))
  let combined ← IO.FS.Handle.mk (output / "samples.jsonl") .write
  let mut completed := #[]
  for block in (← arrField freeze "blocks") do
    let id ← number block "block"
    let session ← number block "session"
    if id > 0 && id % 10 == 0 then
      IO.println s!"counter-fold measurement: session {session + 1} after the frozen 60-second idle interval"
      IO.sleep 60000
    let schedule ← checked (fromJson? (← field block "schedule") : Except String Schedule)
    let order ← (← arrField block "variant_order").mapM string
    let mut accepted := false
    for attempt in [:3] do
      if accepted then break
      let directory := output / s!"session-{session}/block-{id}/attempt-{attempt}"
      IO.FS.createDirAll directory
      let before ← environment core
      writeJson (directory / "environment-start.json") before
      let mut samples := #[]
      let mut reason : Option String := none
      try
        need (← stableEnvironment reference before) "environment drift before block"
        let _ ← inspectBuild build
        for index in [:order.size] do
          let variant := order[index]!
          let hash := digest (← IO.FS.readBinFile (build / s!"bin/{variant}"))
          IO.println s!"counter-fold measurement: session {session + 1}/3, block {id + 1}/30, {variant}"
          let rows ← runScheduled build (directory / s!"{variant}.jsonl") variant schedule core
          for row in rows do
            need ((← number row "peak_rss_kb") <= 2097152) "resource RSS bound exceeded"
            samples := samples.push (enriched row variant id session index attempt buildHash freezeHash hash)
        let after ← environment core
        writeJson (directory / "environment-end.json") after
        need (← stableEnvironment reference after) "environment drift after block"
        let _ ← inspectBuild build
      catch error => reason := some error.toString
      let status := Json.mkObj [("block", toJson id), ("session", toJson session), ("attempt", toJson attempt),
        ("status", toJson (if reason.isSome then "invalid" else "valid")), ("reason", toJson reason), ("samples", toJson samples.size)]
      writeJson (directory / "status.json") status
      if let some failure := reason then
        IO.println s!"counter-fold measurement: retained invalid complete-block attempt {id}/{attempt}: {failure}"
        need (["environment drift", "shorter than 100 ms", "does not dominate timer", "resource RSS bound"].any (fun fragment => failure.contains fragment))
          s!"correctness or artifact failure; publication stopped: {failure}"
      else
        need (samples.size == 228) "counter-fold paired block is incomplete"
        for sample in samples do combined.putStrLn sample.compress
        combined.flush
        completed := completed.push status
        writeJson (output / "progress.json") (Json.mkObj [("valid_blocks", toJson completed), ("complete", toJson false)])
        accepted := true
    need accepted s!"block {id} exhausted three retained attempts"
  let final ← environment core
  writeJson (output / "environment-end.json") final
  need (← stableEnvironment reference final) "environment drift at measurement completion"
  writeJson (output / "measurement.json") (Json.mkObj [("format", toJson "compilatrix/counter-fold-measurement/1"),
    ("build_blake3", toJson buildHash), ("freeze_blake3", toJson freezeHash), ("valid_blocks", toJson completed),
    ("samples", toJson (6840 : Nat)), ("samples_blake3", toJson (digest (← IO.FS.readBinFile (output / "samples.jsonl")))),
    ("status", toJson "complete")])
  IO.println "counter-fold measurement: 6840 samples, all 38 rows, 30 paired blocks, three sessions complete"

end Benchmarks.Compiler.CounterFold
