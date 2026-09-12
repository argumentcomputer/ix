import Benchmark.ScalingBuild

namespace Benchmark.CompilerScaling
open Lean System Compilatrix.Tools.Check Compilatrix.Tools.UniqueCheck

def sessions (profile : String) : Nat := if profile == "smoke" then 1 else 3
def blocksPerSession (profile : String) : Nat := if profile == "smoke" then 1 else 3

def processLimits : Json := Json.mkObj [("address_space_bytes", toJson (4294967296 : Nat)),
  ("maximum_recorded_rss_kib", toJson (2097152 : Nat)),
  ("cpu_seconds", toJson (120 : Nat)), ("wall_seconds", toJson (180 : Nat))]

def orders (profile : String) (rows : Nat) : Array Json := Id.run do
  let mut result := #[]
  for session in [:sessions profile] do
    for localBlock in [:blocksPerSession profile] do
      let block := session * blocksPerSession profile + localBlock
      let seed := (2930098127 + block * 104729).toUInt64
      let order := (shuffled (List.range rows).toArray seed).1
      result := result.push (Json.mkObj [("session", toJson session), ("block", toJson block),
        ("seed", toJson seed.toNat), ("order", toJson order)])
  return result

def samplePath (session block : Nat) (id : String) : String := s!"session-{session}/block-{block}/{id}"

def sampleRecord (directory : FilePath) (row : Json) (rowIndex session block position : Nat)
    (logs : FilePath) (arguments : Array String) : IO Json := do
  let id ← strField row "id"
  artifactCheck directory (← field row "reference")
  let command ← readJson (logs / s!"{id}.command.json")
  let resources ← readJson (logs / s!"{id}.resources.json")
  need ((← number command "exit_code") == 0 && (← number resources "exit_code") == 0 &&
    (← field command "environment_overrides") == toJson workerEnv &&
    (← strField command "command") == "taskset" && (← field command "arguments") == toJson arguments &&
    (← number resources "peak_rss_kb") ≤ 2 * 1024 * 1024) "compiler worker process failed or exceeded its memory budget"
  return Json.mkObj [
    ("row", toJson rowIndex), ("id", toJson id), ("session", toJson session), ("block", toJson block), ("position", toJson position),
    ("metrics", ← readJson (directory / "measurements.json")), ("process", command), ("resources", resources),
    ("stdout_blake3", toJson (digest (← IO.FS.readBinFile (logs / s!"{id}.stdout")))),
    ("stderr_blake3", toJson (digest (← IO.FS.readBinFile (logs / s!"{id}.stderr")))),
    ("stage_journal_blake3", toJson (digest (← IO.FS.readBinFile (directory / "stages.jsonl"))))]

def measureSuite (build correctness output : FilePath) (core : Nat) : IO Unit := do
  let build ← absolute build
  let output ← absolute output
  let metadata ← inspectBuild build
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  let checked ← readJson (correctness / "correctness.json")
  need ((← strField checked "status") == "passed" && (← strField checked "build_blake3") == buildHash)
    "compiler measurement requires correctness for this exact build"
  fresh output
  writeJson (output / "correctness.json") checked
  let profile ← strField metadata "profile"
  let rows ← arrField metadata "rows"
  let timer ← strField metadata "timer_tool"
  let before ← environment core
  let freeze := Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-freeze/1"), ("profile", toJson profile),
    ("build_blake3", toJson buildHash), ("core", toJson core), ("environment", before),
    ("build_path_at_measurement", toJson build.toString), ("measurement_path_at_measurement", toJson output.toString),
    ("worker_blake3", toJson (digest (← IO.FS.readBinFile (build / "tools/compiler-scaling")))),
    ("sessions", toJson (sessions profile)), ("blocks_per_session", toJson (blocksPerSession profile)),
    ("orders", Json.arr (orders profile rows.size)), ("worker_overrides", toJson workerEnv),
    ("process_limits", processLimits)]
  writeJson (output / "freeze.json") freeze
  writeJson (output / "environment-start.json") before
  let samples ← IO.FS.Handle.mk (output / "samples.jsonl") .write
  let mut count := 0
  for plan in orders profile rows.size do
    let session ← number plan "session"
    let block ← number plan "block"
    let blockRoot := output / s!"session-{session}/block-{block}"
    let logs := blockRoot / "logs"
    IO.FS.createDirAll logs
    writeJson (blockRoot / "environment-start.json") (← environment core)
    let order ← (← arrField plan "order").mapM nat
    for position in [:order.size] do
      let rowIndex := order[position]!
      let row := rows[rowIndex]!
      let id ← strField row "id"
      let directory := output / samplePath session block id
      let input := build / (← strField row "input")
      let cache ← field row "cache"
      let extra ← if cache == Json.null then pure #[] else pure #[(build / (← string cache)).toString]
      let arguments := #["compile", input.toString, directory.toString] ++ extra
      runWorker (build / "tools/compiler-scaling") logs id arguments core timer
      let sample ← sampleRecord directory row rowIndex session block position logs
        (launchArgs (build / "tools/compiler-scaling") arguments core)
      samples.putStr (sample.compress ++ "\n")
      samples.flush
      count := count + 1
      IO.println s!"compiler scaling measure: session {session + 1}, block {block + 1}, {id} ({count})"
    let after ← environment core
    writeJson (blockRoot / "environment-end.json") after
    need (← stableEnvironment before after) "compiler measurement environment changed during a block"
  let after ← environment core
  writeJson (output / "environment-end.json") after
  need (← stableEnvironment before after) "compiler measurement environment changed"
  writeJson (output / "measurement.json") (Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-measurement/1"), ("status", toJson "complete"),
    ("build_blake3", toJson buildHash), ("freeze_blake3", toJson (digest (← IO.FS.readBinFile (output / "freeze.json")))),
    ("samples", toJson count), ("samples_blake3", toJson (digest (← IO.FS.readBinFile (output / "samples.jsonl")))),
    ("correctness_blake3", toJson (digest (← IO.FS.readBinFile (output / "correctness.json"))))])

def inspectMeasurement (build measured : FilePath) : IO (Json × Array Json) := do
  let metadata ← inspectBuild build
  let profile ← strField metadata "profile"
  let rows ← arrField metadata "rows"
  let freeze ← readJson (measured / "freeze.json")
  let core ← number freeze "core"
  let originalBuild : FilePath := ← strField freeze "build_path_at_measurement"
  let originalMeasured : FilePath := ← strField freeze "measurement_path_at_measurement"
  let manifest ← readJson (measured / "measurement.json")
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  need ((← strField freeze "format") == "compilatrix/compiler-scaling-freeze/1" &&
    (← strField freeze "profile") == profile && (← number freeze "sessions") == sessions profile &&
    (← field freeze "process_limits") == processLimits &&
    (← number freeze "blocks_per_session") == blocksPerSession profile && (← field freeze "worker_overrides") == toJson workerEnv &&
    (← strField manifest "format") == "compilatrix/compiler-scaling-measurement/1" &&
    (← strField manifest "status") == "complete" && (← strField manifest "build_blake3") == buildHash &&
    (← strField freeze "build_blake3") == buildHash && (← field freeze "orders") == Json.arr (orders profile rows.size) &&
    (← strField manifest "freeze_blake3") == digest (← IO.FS.readBinFile (measured / "freeze.json")) &&
    (← strField freeze "worker_blake3") == digest (← IO.FS.readBinFile (build / "tools/compiler-scaling"))) "compiler measurement freeze or build changed"
  let count := rows.size * sessions profile * blocksPerSession profile
  let combined ← readLines (measured / "samples.jsonl")
  need (combined.size == count && (← number manifest "samples") == count &&
    (← strField manifest "samples_blake3") == digest (← IO.FS.readBinFile (measured / "samples.jsonl"))) "compiler sample inventory or digest changed"
  need ((← strField manifest "correctness_blake3") == digest (← IO.FS.readBinFile (measured / "correctness.json"))) "compiler correctness record changed"
  let checked ← readJson (measured / "correctness.json")
  need ((← strField checked "status") == "passed" && (← strField checked "build_blake3") == buildHash) "compiler correctness is for a different build"
  let initial ← field freeze "environment"
  for file in ["environment-start.json", "environment-end.json"] do
    need (← stableEnvironment initial (← readJson (measured / file))) "compiler measurement environment drift"
  let mut reconstructed := #[]
  for plan in orders profile rows.size do
    let session ← number plan "session"
    let block ← number plan "block"
    let blockRoot := measured / s!"session-{session}/block-{block}"
    for file in ["environment-start.json", "environment-end.json"] do
      need (← stableEnvironment initial (← readJson (blockRoot / file))) "compiler block environment drift"
    let order ← (← arrField plan "order").mapM nat
    for position in [:order.size] do
      let index := order[position]!
      let row := rows[index]!
      let relative := samplePath session block (← strField row "id")
      let directory := measured / relative
      let cache ← field row "cache"
      let extra ← if cache == Json.null then pure #[] else pure #[(originalBuild / (← string cache)).toString]
      let arguments := #["compile", (originalBuild / (← strField row "input")).toString, (originalMeasured / relative).toString] ++ extra
      reconstructed := reconstructed.push (← sampleRecord directory row index session block position (blockRoot / "logs")
        (launchArgs (originalBuild / "tools/compiler-scaling") arguments core))
  -- GNU time may write 0.00 while Json.compress writes 0. Compare the
  -- canonical serialization so equivalent decimal spellings round-trip.
  need ((Json.arr combined).compress == (Json.arr reconstructed).compress)
    "compiler combined samples differ from complete raw process records"
  return (metadata, reconstructed)

/-- Deliberately corrupt retained records, including their outer digests, to
exercise schedule, completeness, journal, and raw/combined agreement checks. -/
def measurementRegressions (build measured output : FilePath) : IO Unit := do
  fresh output
  let copied := output / "measured"
  let _ ← run "cp" #["-R", measured.toString, copied.toString]
  let manifest ← readJson (copied / "measurement.json")
  let freeze ← readJson (copied / "freeze.json")
  let samples ← readLines (copied / "samples.jsonl")
  let writeSamples := fun rows => IO.FS.writeFile (copied / "samples.jsonl")
    (String.intercalate "\n" (rows.toList.map Json.compress) ++ "\n")
  let check := fun reason => rejects reason reason (inspectMeasurement build copied *> pure ())
  let refreshSamples := do
    writeJson (copied / "measurement.json") (← replaceAt manifest ["samples_blake3"]
      (toJson (digest (← IO.FS.readBinFile (copied / "samples.jsonl")))))
  writeSamples samples.pop
  refreshSamples
  check "compiler sample inventory"
  writeSamples samples
  writeJson (copied / "measurement.json") manifest
  writeJson (copied / "freeze.json") (← replaceAt freeze ["orders"] (Json.arr #[]))
  writeJson (copied / "measurement.json") (← replaceAt manifest ["freeze_blake3"]
    (toJson (digest (← IO.FS.readBinFile (copied / "freeze.json")))))
  check "compiler measurement freeze"
  writeJson (copied / "freeze.json") freeze
  writeJson (copied / "measurement.json") manifest
  let altered ← replaceAt samples[0]! ["position"] (toJson (999 : Nat))
  writeSamples (samples.set! 0 altered)
  refreshSamples
  check "compiler combined samples"
  writeSamples samples
  writeJson (copied / "measurement.json") manifest
  let sample := samples[0]!
  let path := copied / samplePath (← number sample "session") (← number sample "block") (← strField sample "id") / "stages.jsonl"
  let journal ← IO.FS.readFile path
  IO.FS.writeFile path (journal ++ (← arrField (← field sample "metrics") "stages")[0]!.compress ++ "\n")
  check "compiler stage journal disagrees"
  IO.FS.writeFile path journal
  writeJson (output / "regressions.json") (Json.mkObj [("status", toJson "passed"), ("cases", toJson (4 : Nat))])

end Benchmark.CompilerScaling
