import Benchmarks.Compiler.CounterFoldRun
import Benchmarks.Compiler.Reproduce

namespace Benchmarks.Compiler.CounterFold
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def inspectProcess (process : Json) (variant executableHash stdoutHash : String) (core : Nat) (schedule : Schedule) : IO Unit := do
  need ((← strField process "variant") == variant && (← strField process "executable_blake3") == executableHash &&
    (← number process "exit_code") == 0 && (← number process "core") == core &&
    (← field process "schedule") == toJson schedule &&
    (← strField process "schedule_blake3") == digest schedule.bytes &&
    (← strField process "stdout_blake3") == stdoutHash) "counter-fold raw process identity disagrees"

def inspectMeasurement (build measured : FilePath) : IO (Json × Array ObservedBlock) := do
  requireCorrectness build measured
  let freeze ← inspectFreeze build measured
  let manifest ← readJson (measured / "measurement.json")
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  let freezeHash := digest (← IO.FS.readBinFile (measured / "freeze.json"))
  need ((← strField manifest "format") == "compilatrix/counter-fold-measurement/1" &&
    (← strField manifest "status") == "complete" && (← number manifest "samples") == 6840 &&
    (← strField manifest "build_blake3") == buildHash && (← strField manifest "freeze_blake3") == freezeHash &&
    (← strField manifest "samples_blake3") == digest (← IO.FS.readBinFile (measured / "samples.jsonl")))
    "counter-fold measurement inventory or digest disagrees"
  let reference ← field freeze "environment"
  let core ← number freeze "core"
  for file in ["environment-start.json", "environment-end.json"] do
    need (← stableEnvironment reference (← readJson (measured / file))) "counter-fold measurement environment drift"
  let valid ← arrField manifest "valid_blocks"
  need (valid.size == 30) "counter-fold paired block inventory disagrees"
  let mut observations := #[]
  let mut reconstructed := #[]
  for block in (← arrField freeze "blocks") do
    let id ← number block "block"
    let session ← number block "session"
    let status := valid[id]!
    let attempt ← number status "attempt"
    need ((← number status "block") == id && (← number status "session") == session &&
      (← strField status "status") == "valid" && (← field status "reason") == Json.null &&
      (← number status "samples") == 228 && attempt < 3) "counter-fold valid block identity disagrees"
    let directory := measured / s!"session-{session}/block-{id}/attempt-{attempt}"
    need ((← readJson (directory / "status.json")) == status) "counter-fold retained block status disagrees"
    for file in ["environment-start.json", "environment-end.json"] do
      need (← stableEnvironment reference (← readJson (directory / file))) "counter-fold valid block environment drift"
    let schedule ← checked (fromJson? (← field block "schedule") : Except String Schedule)
    let order ← (← arrField block "variant_order").mapM string
    let mut samples := Array.replicate 38 (Array.replicate 2 #[])
    let mut initialRss := Array.replicate 2 0
    for index in [:order.size] do
      let variant := order[index]!
      let variantIndex ← present (variants.toList.idxOf? variant) "unknown measured variant"
      let path := directory / s!"{variant}.jsonl"
      let rows ← readLines path
      let native ← inspectRun "compilatrix" schedule rows true
      initialRss := initialRss.set! variantIndex (← number rows[0]! "initial_rss_kb")
      let process ← readJson (path.withExtension "process.json")
      let hash := digest (← IO.FS.readBinFile (build / s!"bin/{variant}"))
      let stdoutHash := digest (← IO.FS.readBinFile path)
      inspectProcess process variant hash stdoutHash core schedule
      need ((← IO.FS.readBinFile (path.withExtension "bin")) == schedule.bytes) "counter-fold raw binary schedule drift"
      if id == 0 then
        for (key, value) in [("variant", toJson "unknown"), ("executable_blake3", toJson "wrong"),
            ("stdout_blake3", toJson "wrong"), ("core", toJson (core + 1)), ("exit_code", toJson (1 : Nat))] do
          rejects key "raw process identity" (inspectProcess (← replaceAt process [key] value) variant hash stdoutHash core schedule)
      for sample in native do
        let row ← number sample "row"
        need ((← number sample "peak_rss_kb") <= 2097152) "counter-fold valid block exceeded RSS bound"
        samples := samples.set! row (samples[row]!.set! variantIndex (samples[row]![variantIndex]!.push sample))
        reconstructed := reconstructed.push (enriched sample variant id session index attempt buildHash freezeHash hash)
    need (samples.all (fun row => row.all (·.size == 3))) "counter-fold block has missing paired rows"
    observations := observations.push { samples, upstream := #[], initialRss }
  need ((← readLines (measured / "samples.jsonl")) == reconstructed) "counter-fold combined samples differ from paired raw process records"
  return (freeze, observations)

def analyzeSuite (build measured output : FilePath) : IO Unit := do
  fresh output
  analysisSelfCheck
  let (freeze, blocks) ← inspectMeasurement build measured
  let hash := digest (← IO.FS.readBinFile (build / "build.json"))
  freezeRegressions hash freeze
  let indices := bootstrapIndices
  let mut results := #[]
  let mut report := "# Checked reserve/reuse counter folding\n\n" ++
    "One source function, two checked native lowerings, and identical C driver objects. " ++
    "The only loop rewrite removes four cancelling reservation/live counter changes (12 instructions per element). " ++
    "Every cell operation and cumulative reuse/payload counter update remains.\n\n" ++
    "Each row contains 30 paired blocks across three sessions, using each variant's median of three native samples per block. " ++
    "Operation counts are common within each row and frozen before measurement. Samples accumulate at least 100 ms. " ++
    "The paired speedup is baseline time divided by folded time; values above one favor folding. " ++
    "The 95% intervals use 10,000 hierarchical paired bootstrap draws, resampling sessions and then blocks (seed 2671931027). " ++
    "All valid slow samples are retained and the timer control is not subtracted. " ++
    "This is a shared host with a pinned worker, uncontrolled SMT sibling and only three session clusters; it establishes no CI timing threshold.\n\n"
  for profile in [:2] do
    report := report ++ s!"## {if profile == 0 then "Entry plus handoff" else "Complete lifecycle"}\n\n" ++
      "Nanoseconds per operation; lifecycle includes fresh construction, reversal, digest and full reclamation.\n\n" ++
      "| Length | Domain | Baseline ns | Folded ns | Paired speedup [95% interval] |\n" ++
      "| ---: | --- | ---: | ---: | ---: |\n"
    for localId in [:19] do
      let id := profile * 19 + localId
      let specification := timingCases[id]!
      let values ← variants.mapIdxM fun variantIndex _ => blocks.mapM fun block => do
        return median (← block.samples[id]![variantIndex]!.mapM nsPerOp)
      let stats := values.map (distribution indices)
      let ratio := distribution indices (values[0]!.zipWith (· / ·) values[1]!)
      let row := Json.mkObj [("row", toJson id), ("case", specification.json),
        ("baseline_ns_per_operation", stats[0]!), ("folded_ns_per_operation", stats[1]!),
        ("paired_speedup_baseline_over_folded", ratio)]
      results := results.push row
      report := report ++ s!"| {specification.length} | {domainName specification.domain} | " ++
        s!"{compactFloat (median values[0]!)} | {compactFloat (median values[1]!)} | " ++
        s!"{compactFloat (← statistic ratio "median")} [{compactFloat (← statistic ratio "ci95_low")}, {compactFloat (← statistic ratio "ci95_high")}] |\n"
    report := report ++ "\n"
  let mut resources := #[]
  let mut code := #[]
  report := report ++ "## Code and checking work\n\n" ++
    "The object text sizes below isolate the checked reversal and release functions. " ++
    "Generation and independent-gate CPU/wall/RSS records are diagnostic envelopes: generation includes pipeline construction and modeled fixture executions; " ++
    "each gate includes two fresh generations, decoding, corruption checks and a linked native harness. " ++
    "They are retained as complete costs, without attributing them to an isolated compiler or proof-checker phase.\n\n" ++
    "| Variant | Reversal `.text` bytes | Release `.text` bytes | Producer wall s | Gate wall s |\n" ++
    "| --- | ---: | ---: | ---: | ---: |\n"
  for variant in variants do
    let mut sizes := #[]
    for role in ["main", "release"] do
      let text ← IO.FS.readFile (build / s!"diagnostics/build/size-{variant}-{role}.stdout")
      let line ← present ((text.splitOn "\n").find? (fun line => (words line).head? == some ".text")) "missing object text size"
      let size ← present ((words line)[1]?.bind String.toNat?) "invalid object text size"
      sizes := sizes.push size
    let generation ← readJson (build / s!"diagnostics/build/produce-{variant}.resources.json")
    let gate ← readJson (build / s!"diagnostics/build/independent-gate-{variant}.resources.json")
    let pipeline ← IO.FS.readBinFile (build / s!"artifacts/{variant}/pipeline.json")
    code := code.push (Json.mkObj [("variant", toJson variant), ("main_text_bytes", toJson sizes[0]!),
      ("release_text_bytes", toJson sizes[1]!), ("pipeline_json_bytes", toJson pipeline.size),
      ("generation_envelope", generation), ("independent_gate_envelope", gate)])
    report := report ++ s!"| {variant} | {sizes[0]!} | {sizes[1]!} | {← statistic generation "wall_seconds"} | {← statistic gate "wall_seconds"} |\n"
  for index in [:2] do
    let mut peak := 0
    let mut currentMin : Option Nat := none
    let mut currentMax := 0
    for block in blocks do
      for row in block.samples do
        for sample in row[index]! do
          let rss ← number sample "rss_kb"
          currentMin := some (min rss (currentMin.getD rss))
          currentMax := max currentMax rss
          peak := max peak (← number sample "peak_rss_kb")
    resources := resources.push (Json.mkObj [("variant", toJson variants[index]!),
      ("ready_rss_kb_median", toJson (median (blocks.map (fun block => block.initialRss[index]!.toFloat)))),
      ("minimum_sample_rss_kb", toJson currentMin), ("maximum_sample_rss_kb", toJson currentMax),
      ("maximum_recorded_peak_rss_kb", toJson peak)])
  writeJson (output / "summary.json") (Json.mkObj [("format", toJson "compilatrix/counter-fold-analysis/1"),
    ("build_blake3", toJson hash), ("freeze_blake3", toJson (digest (← IO.FS.readBinFile (measured / "freeze.json")))),
    ("measurement_blake3", toJson (digest (← IO.FS.readBinFile (measured / "measurement.json")))),
    ("environment", ← field freeze "environment"), ("timing_policy", timingPolicy), ("results", toJson results),
    ("code_and_checking", toJson code), ("process_memory", toJson resources)])
  IO.FS.writeFile (output / "report.md") report
  IO.println "counter-fold analysis: 38 paired comparisons, uncertainty, code/checking costs and process memory validated"

def reproduceSuite (build measured output : FilePath) : IO Unit := do
  let build ← absolute build
  let measured ← absolute measured
  let output ← absolute output
  let (_, _) ← inspectMeasurement build measured
  fresh output
  let metadata ← inspectBuild build
  let environment ← checked (fromJson? (← field metadata "build_environment") : Except String (Array (String × Option String)))
  need (environment.map Prod.fst == buildEnvNames) "counter-fold replay environment inventory disagrees"
  for row in (← array (← readJson (build / "tool-identities.json"))) do
    need (digest (← IO.FS.readBinFile (← strField row "resolved")) == (← strField row "blake3")) "counter-fold installed tool drift"
  let snapshot ← readJson (build / "source.json")
  need (digest (← IO.FS.readBinFile (build / "source.tar.gz")) == (← strField snapshot "archive_blake3")) "counter-fold source archive digest disagrees"
  let source := output / "source"
  IO.FS.createDirAll source
  let inventory ← arrField snapshot "files"
  let names ← inventory.mapM (fun row => strField row "path")
  need (names.toList.Nodup && names.all (fun name => !name.startsWith "/" &&
    !(name.splitOn "/").any (fun part => part == ".." || part.isEmpty))) "unsafe counter-fold source inventory"
  let listing := (← run "tar" #["-tzf", (build / "source.tar.gz").toString]).trimAscii.toString.splitOn "\n"
  need (listing.mergeSort (· ≤ ·) == names.toList.mergeSort (· ≤ ·)) "counter-fold source tar inventory disagrees"
  let _ ← run "tar" #["--no-same-owner", "--no-same-permissions", "-xzf", (build / "source.tar.gz").toString, "-C", source.toString]
  for row in inventory do
    let bytes ← IO.FS.readBinFile (source / (← strField row "path"))
    need (bytes.size == (← number row "bytes") && digest bytes == (← strField row "blake3")) "counter-fold extracted source differs"
  IO.FS.createDirAll (source / ".lake/build/bin")
  for path in (← files (build / "tools-bin")) do
    let _ ← run "cp" #[path.toString, (source / ".lake/build/bin" / path.fileName.getD "missing").toString]
  let runner := (source / ".lake/build/bin/compiler-benchmark").toString
  let rebuilt := output / "build"
  replayCommand source environment runner #["counter-fold-build", rebuilt.toString, "--gcc", ← strField metadata "gcc",
    "--time", ← strField metadata "timer_tool"] (output / "rebuild.jsonl")
  let rebuiltMetadata ← inspectBuild rebuilt
  for key in ["artifacts", "executables", "tools", "goldens", "datasets_blake3", "protocol_blake3"] do
    need ((← field rebuiltMetadata key) == (← field metadata key)) s!"counter-fold independent rebuild changed {key}"
  replayCommand source environment runner #["counter-fold-verify", rebuilt.toString, (output / "correctness").toString] (output / "verify.jsonl")
  let original ← arrField (← readJson (measured / "correctness.json")) "matrices"
  let repeated ← arrField (← readJson (output / "correctness/correctness.json")) "matrices"
  need (original.size == 2 && repeated.size == 2) "counter-fold replay matrix inventory changed"
  for i in [:2] do
    need ((← field original[i]! "result") == (← field repeated[i]! "result")) "counter-fold independent matrix differs"
  replayCommand source environment runner #["counter-fold-analyze", build.toString, measured.toString,
    (output / "analysis").toString] (output / "analysis.jsonl")
  for file in ["summary.json", "report.md"] do
    need ((← IO.FS.readBinFile (output / "analysis" / file)) == (← IO.FS.readBinFile (measured / "analysis" / file)))
      s!"counter-fold independent analysis changed {file}"
  writeJson (output / "reproduction.json") (Json.mkObj [("format", toJson "compilatrix/counter-fold-reproduction/1"),
    ("source_archive_blake3", ← field snapshot "archive_blake3"), ("original_build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))),
    ("rebuilt_build_blake3", toJson (digest (← IO.FS.readBinFile (rebuilt / "build.json")))), ("source_files", toJson inventory.size),
    ("artifacts_exact", toJson true), ("executables_exact", toJson true), ("correctness_exact", toJson true), ("analysis_exact", toJson true),
    ("scope", toJson "fresh extracted source, empty process environment plus recorded variables, hashed producer/checker seeds, same host and pinned Nix closure"),
    ("timing_samples_rerun", toJson false), ("status", toJson "passed")])
  IO.println "counter-fold reproduction: exact rebuilt objects, executables, complete results and retained-sample analysis passed"

end Benchmarks.Compiler.CounterFold
