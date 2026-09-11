import Benchmarks.Compiler.Pilot

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def inspectFreeze (build pilot : FilePath) : IO Json := do
  let freeze ← readJson (pilot / "freeze.json")
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  need ((← strField freeze "format") == "compilatrix/benchmark-freeze/1" &&
    (← strField freeze "build_blake3") == buildHash) "frozen schedule belongs to a different build"
  let manifest ← readJson (build / "manifest.json")
  need ((← number freeze "minimum_sample_ns") == minimumNs && (← number freeze "pilot_target_ns") == pilotTargetNs &&
    (← number freeze "order_seed") == orderSeed.toNat && (← number freeze "resource_bound_rss_kb") == 2097152 &&
    (← number freeze "timer_chunk_minimum_factor") == 100 && (← number freeze "session_separation_seconds") == 60 &&
    (← number freeze "bootstrap_replicates") == 10000 && (← number freeze "bootstrap_seed") == 2671931027 &&
    (← field freeze "bootstrap") == (← field (← field manifest "analysis") "bootstrap")) "frozen timing/analysis policy changed"
  let blocks ← arrField freeze "blocks"
  need (blocks.size == blockCount) "frozen block inventory disagrees"
  let mut common : Option (Array Nat) := none
  let mut state := orderSeed
  for index in [:blocks.size] do
    let block := blocks[index]!
    need ((← number block "block") == index && (← number block "session") == index / 10) "frozen block/session identity disagrees"
    let schedule ← checked (fromJson? (← field block "schedule") : Except String Schedule)
    need (schedule.valid && schedule.mode == 2) "frozen measurement schedule invalid"
    let order ← (← arrField block "implementation_order").mapM string
    need (order.toList.mergeSort (· ≤ ·) == implementations.toList.mergeSort (· ≤ ·)) "frozen comparison inventory disagrees"
    let (expectedRows, next) := shuffled (List.range 38).toArray state
    let (expectedImplementations, next) := shuffled (List.range 6).toArray next
    state := next
    need (schedule.order == expectedRows && order == expectedImplementations.map (implementations[·]!)) "frozen randomized order changed"
    if let some counts := common then need (counts == schedule.operations) "frozen counts vary across blocks"
    common := some schedule.operations
  let upstream ← arrField freeze "upstream"
  need (upstream.size == 2) "frozen upstream inventory changed"
  for i in [:2] do
    need ((← strField upstream[i]! "name") == (if i == 0 then "applyClosed" else "letClosed") &&
      (← number upstream[i]! "value") == i + 3 && (← number upstream[i]! "operations") > 0 &&
      (← number upstream[i]! "operations") <= 100000000000 && (← number upstream[i]! "operations") % (chunkSize * 6) == 0)
      "frozen upstream counts or values changed"
  return freeze

def enriched (sample : Json) (block session order attempt : Nat) (buildHash freezeHash executableHash : String) : Json :=
  let row := (sample.getObjValAs? Nat "row").toOption.map (timingCases[·]!)
  Json.mkObj [("format", toJson "compilatrix/benchmark-sample/1"), ("block", toJson block), ("session", toJson session),
    ("workload", toJson (if row.isSome then workload else "upstream-closed-nat")),
    ("profile", toJson (row.map TimingCase.profileName |>.getD "native-call")),
    ("case", row.map TimingCase.json |>.getD (Json.mkObj [("runtime_arguments", toJson (0 : Nat))])),
    ("dataset_seeds", row.map (fun row => toJson (row.inputIds.map (fun id => inputs[id]!.seed.toNat))) |>.getD Json.null),
    ("order", toJson order), ("attempt", toJson attempt), ("build_blake3", toJson buildHash),
    ("freeze_blake3", toJson freezeHash), ("executable_blake3", toJson executableHash),
    ("dataset_blake3", toJson (digest datasetBytes)), ("status", toJson "valid"), ("observation", sample)]

def measureSuite (build correctness pilot output : FilePath) (core : Nat) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  requireCorrectness build correctness
  let freeze ← inspectFreeze build pilot
  need ((← number freeze "core") == core) "measurement core differs from frozen pilot"
  let reference ← field freeze "environment"
  let initial ← environment core
  need (← stableEnvironment reference initial) "measurement environment differs from pilot"
  fresh output
  IO.FS.writeFile (output / "freeze.json") (← IO.FS.readFile (pilot / "freeze.json"))
  IO.FS.writeFile (output / "correctness.json") (← IO.FS.readFile (correctness / "correctness.json"))
  writeJson (output / "environment-start.json") initial
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  let freezeHash := digest (← IO.FS.readBinFile (output / "freeze.json"))
  let allSamples ← IO.FS.Handle.mk (output / "samples.jsonl") .write
  let upstreamSamples ← IO.FS.Handle.mk (output / "upstream.jsonl") .write
  let mut completed := #[]
  for block in (← arrField freeze "blocks") do
    let id ← number block "block"
    let session ← number block "session"
    if id > 0 && id % 10 == 0 then
      IO.println s!"benchmark measurement: session {session} starts after the frozen 60-second idle interval"
      IO.sleep 60000
    let schedule ← checked (fromJson? (← field block "schedule") : Except String Schedule)
    let order ← (← arrField block "implementation_order").mapM string
    let mut accepted := false
    for attempt in [:3] do
      if accepted then break
      let directory := output / s!"session-{session}/block-{id}/attempt-{attempt}"
      IO.FS.createDirAll directory
      let before ← environment core
      writeJson (directory / "environment-start.json") before
      let mut samples := #[]
      let mut upstreamRows := #[]
      let mut reason : Option String := none
      try
        need (← stableEnvironment reference before) "environment drift before block"
        let _ ← inspectBuild build
        for orderIndex in [:order.size] do
          let implementation := order[orderIndex]!
          let hash := digest (← IO.FS.readBinFile (build / s!"bin/{implementation}"))
          IO.println s!"benchmark measurement: session {session + 1}/3, block {id + 1}/30, {implementation}"
          let rows ← runScheduled build (directory / s!"{implementation}.jsonl") implementation schedule core
          for row in rows do
            need ((← number row "peak_rss_kb") <= (← number freeze "resource_bound_rss_kb")) "resource RSS bound exceeded"
            samples := samples.push (enriched row id session orderIndex attempt buildHash freezeHash hash)
        let upstream := (← arrField freeze "upstream")
        let upstream := if id % 2 == 0 then upstream else upstream.reverse
        for upstreamOrder in [:upstream.size] do
          let entry := upstream[upstreamOrder]!
          let name ← strField entry "name"
          let value ← number entry "value"
          let operations ← number entry "operations"
          let rows ← runUpstream build (directory / s!"upstream-{name}.jsonl") name value operations 3 core true
          let hash := digest (← IO.FS.readBinFile (build / s!"bin/upstream-{name}"))
          for row in rows do
            need ((← number row "peak_rss_kb") <= (← number freeze "resource_bound_rss_kb")) "resource RSS bound exceeded"
            upstreamRows := upstreamRows.push (Json.mkObj [("name", toJson name),
              ("sample", enriched row id session upstreamOrder attempt buildHash freezeHash hash)])
        let after ← environment core
        writeJson (directory / "environment-end.json") after
        need (← stableEnvironment reference after) "environment drift after block"
        let _ ← inspectBuild build
      catch error => reason := some error.toString
      let status := Json.mkObj [("block", toJson id), ("session", toJson session), ("attempt", toJson attempt),
        ("status", toJson (if reason.isSome then "invalid" else "valid")), ("reason", toJson reason),
        ("samples", toJson samples.size), ("upstream_samples", toJson upstreamRows.size)]
      writeJson (directory / "status.json") status
      if let some failure := reason then
        IO.println s!"benchmark measurement: retained invalid complete-block attempt {id}/{attempt}: {failure}"
        -- Only environmental/timing validity failures admit a complete-block
        -- rerun. A failed result, parser, process, or artifact stops the run.
        need (["environment drift", "shorter than 100 ms", "does not dominate timer", "resource RSS bound"].any (fun fragment => failure.contains fragment))
          s!"correctness or artifact failure; publication stopped: {failure}"
      else
        need (samples.size == 684 && upstreamRows.size == 6) "valid block is incomplete"
        for sample in samples do allSamples.putStrLn sample.compress
        for sample in upstreamRows do upstreamSamples.putStrLn sample.compress
        allSamples.flush
        upstreamSamples.flush
        completed := completed.push status
        writeJson (output / "progress.json") (Json.mkObj [("valid_blocks", Json.arr completed), ("complete", toJson false)])
        accepted := true
    need accepted s!"block {id} exhausted three recorded attempts; no complete report"
  let final ← environment core
  writeJson (output / "environment-end.json") final
  need (← stableEnvironment reference final) "environment drift at measurement completion"
  writeJson (output / "measurement.json") (Json.mkObj [("format", toJson "compilatrix/benchmark-measurement/1"),
    ("build_blake3", toJson buildHash), ("freeze_blake3", toJson freezeHash), ("valid_blocks", Json.arr completed),
    ("samples", toJson (20520 : Nat)), ("upstream_samples", toJson (180 : Nat)),
    ("samples_blake3", toJson (digest (← IO.FS.readBinFile (output / "samples.jsonl")))),
    ("upstream_blake3", toJson (digest (← IO.FS.readBinFile (output / "upstream.jsonl")))), ("status", toJson "complete")])
  IO.println "benchmark measurement: all six implementations and two upstream entries completed 30 blocks across three sessions"

end Benchmarks.Compiler
