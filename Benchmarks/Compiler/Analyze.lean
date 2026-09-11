import Benchmarks.Compiler.Measure

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def quantile (values : Array Float) (numerator denominator : Nat) : Float := Id.run do
  if values.isEmpty then return 0
  let sorted := values.qsort (· < ·)
  let position := numerator * (values.size - 1)
  let left := position / denominator
  let fraction := (position % denominator).toFloat / denominator.toFloat
  return sorted[left]! * (1 - fraction) + sorted[min (left + 1) (values.size - 1)]! * fraction

def median (values : Array Float) : Float := quantile values 1 2

/-- The same index vectors apply to every implementation and every ratio.
Sessions are the outer cluster, and each selected session contributes ten
paired blocks sampled with replacement. -/
def bootstrapIndices (seed : UInt64 := 2671931027) (replicates : Nat := 10000) : Array (Array Nat) := Id.run do
  let mut state := seed
  let mut result := #[]
  for _ in [:replicates] do
    let mut indices := #[]
    for _ in [:3] do
      state := nextRandom state
      let session := state.toNat % 3
      for _ in [:10] do
        state := nextRandom state
        indices := indices.push (session * 10 + state.toNat % 10)
    result := result.push indices
  return result

def distribution (indices : Array (Array Nat)) (values : Array Float) : Json :=
  let bootstraps := indices.map fun sample => median (sample.map (values[·]!))
  Json.mkObj [("blocks", toJson values.size), ("median", toJson (median values)),
    ("q25", toJson (quantile values 1 4)), ("q75", toJson (quantile values 3 4)),
    ("ci95_low", toJson (quantile bootstraps 1 40)), ("ci95_high", toJson (quantile bootstraps 39 40)),
    ("session_medians", toJson ((List.range 3).map fun session => median (values.extract (session * 10) ((session + 1) * 10))))]

def numeric (json : Json) : IO Float := do
  let value ← checked (fromJson? json : Except String Float)
  need (value.isFinite && value > 0) "analysis expects finite positive numeric observations"
  return value

def statistic (json : Json) (name : String) : IO Float := do numeric (← field json name)

def analysisSelfCheck : IO Unit := do
  let values := (List.range 30).toArray.map (fun n => (n + 1).toFloat)
  need (median values == 15.5 && quantile values 1 4 == 8.25 && quantile values 3 4 == 22.75)
    "analysis quantile regression"
  let indices := bootstrapIndices 2671931027 1000
  need (indices == bootstrapIndices 2671931027 1000 && indices.size == 1000 &&
    indices.all (fun row => row.size == 30 && row.all (· < 30))) "analysis bootstrap is not reproducible or bounded"
  for row in indices do
    for cluster in [:3] do
      let segment := row.extract (cluster * 10) ((cluster + 1) * 10)
      need (segment.all (fun index => index / 10 == segment[0]! / 10)) "bootstrap broke a session cluster"
  let ratios := values.map (fun value => (2 * value) / value)
  let result := distribution indices ratios
  for key in ["median", "q25", "q75", "ci95_low", "ci95_high"] do
    need ((← statistic result key) == 2) "paired ratio bootstrap lost pairing"
  rejects "zero analysis input" "finite positive" (numeric (toJson (0 : Nat)) *> pure ())
  IO.println "benchmark analysis self-check: quantiles, deterministic hierarchical session clusters, paired ratios, and invalid numeric inputs passed"

structure ObservedBlock where
  -- Stable layout: row ID, implementation, then the three native observations.
  samples : Array (Array (Array Json))
  upstream : Array (Array Json)
  initialRss : Array Nat

def inspectMeasurement (build measured : FilePath) : IO (Json × Array ObservedBlock) := do
  let metadata ← inspectBuild build
  let freeze ← inspectFreeze build measured
  let manifest ← readJson (measured / "measurement.json")
  need ((← strField manifest "format") == "compilatrix/benchmark-measurement/1" &&
    (← strField manifest "status") == "complete") "measurement is not complete"
  let buildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  let freezeHash := digest (← IO.FS.readBinFile (measured / "freeze.json"))
  need ((← strField manifest "build_blake3") == buildHash && (← strField manifest "freeze_blake3") == freezeHash)
    "measurement build/freeze identity disagrees"
  for (name, key) in [("samples.jsonl", "samples_blake3"), ("upstream.jsonl", "upstream_blake3")] do
    need (digest (← IO.FS.readBinFile (measured / name)) == (← strField manifest key)) "retained sample digest disagrees"
  let correctness ← readJson (measured / "correctness.json")
  need ((← strField correctness "build_blake3") == buildHash && (← strField correctness "status") == "passed" &&
    (← field correctness "executables") == (← field metadata "executables")) "measurement correctness record differs"
  let reference ← field freeze "environment"
  for file in ["environment-start.json", "environment-end.json"] do
    need (← stableEnvironment reference (← readJson (measured / file))) "measurement environment drift"
  let valid ← arrField manifest "valid_blocks"
  need (valid.size == 30 && (← number manifest "samples") == 20520 && (← number manifest "upstream_samples") == 180)
    "measurement block/sample inventory disagrees"
  let mut observations := #[]
  let mut reconstructed := #[]
  let mut upstreamReconstructed := #[]
  for block in (← arrField freeze "blocks") do
    let id ← number block "block"
    let session ← number block "session"
    let status := valid[id]!
    let attempt ← number status "attempt"
    need ((← number status "block") == id && (← number status "session") == session &&
      (← strField status "status") == "valid" && attempt < 3) "valid block identity disagrees"
    let directory := measured / s!"session-{session}/block-{id}/attempt-{attempt}"
    need ((← readJson (directory / "status.json")) == status) "retained block status disagrees"
    for file in ["environment-start.json", "environment-end.json"] do
      need (← stableEnvironment reference (← readJson (directory / file))) "valid block has environmental drift"
    let schedule ← checked (fromJson? (← field block "schedule") : Except String Schedule)
    let order ← (← arrField block "implementation_order").mapM string
    let mut samples := Array.replicate 38 (Array.replicate 6 #[])
    let mut initialRss := Array.replicate 6 0
    for orderIndex in [:order.size] do
      let implementation := order[orderIndex]!
      let implementationIndex ← present (implementations.toList.idxOf? implementation) "unknown measured implementation"
      let path := directory / s!"{implementation}.jsonl"
      let rows ← readLines path
      let native ← inspectRun implementation schedule rows true
      initialRss := initialRss.set! implementationIndex (← number rows[0]! "initial_rss_kb")
      let process ← readJson (path.withExtension "process.json")
      need ((← number process "exit_code") == 0 && (← field process "schedule") == toJson schedule &&
        (← number process "core") == (← number freeze "core") && (← strField process "implementation") == implementation &&
        (← strField process "schedule_blake3") == digest schedule.bytes &&
        (← strField process "stdout_blake3") == digest (← IO.FS.readBinFile path)) "raw process identity disagrees"
      need ((← IO.FS.readBinFile (path.withExtension "bin")) == schedule.bytes) "raw binary schedule drifted"
      let hash := digest (← IO.FS.readBinFile (build / s!"bin/{implementation}"))
      for sample in native do
        let row ← number sample "row"
        need ((← number sample "peak_rss_kb") <= (← number freeze "resource_bound_rss_kb")) "valid block exceeded RSS limit"
        samples := samples.set! row (samples[row]!.set! implementationIndex (samples[row]![implementationIndex]!.push sample))
        reconstructed := reconstructed.push (enriched sample id session orderIndex attempt buildHash freezeHash hash)
    let entries ← arrField freeze "upstream"
    need (entries.size == 2) "upstream measured inventory changed"
    let entries := if id % 2 == 0 then entries else entries.reverse
    let mut upstream := Array.replicate 2 #[]
    for upstreamOrder in [:entries.size] do
      let entry := entries[upstreamOrder]!
      let name ← strField entry "name"
      let index := if name == "applyClosed" then 0 else 1
      need (name == (if index == 0 then "applyClosed" else "letClosed")) "unknown upstream measured entry"
      let value ← number entry "value"
      let operations ← number entry "operations"
      let rows ← readLines (directory / s!"upstream-{name}.jsonl")
      need (rows.size == 4 && (← kind rows[0]!) == "warmup" && (← number rows[0]! "elapsed_ns") >= 1000000000)
        "upstream native warm-up/sample inventory disagrees"
      let hash := digest (← IO.FS.readBinFile (build / s!"bin/upstream-{name}"))
      for i in [:3] do
        let row := rows[i + 1]!
        need ((← kind row) == "sample" && (← number row "sample") == i &&
          (← number row "operations") == operations && (← number row "elapsed_ns") >= minimumNs &&
          (← number row "sink") == operations * value &&
          (← number row "peak_rss_kb") <= (← number freeze "resource_bound_rss_kb")) "upstream native sample identity, value or resource bound disagrees"
        upstreamReconstructed := upstreamReconstructed.push (Json.mkObj [("name", toJson name),
          ("sample", enriched row id session upstreamOrder attempt buildHash freezeHash hash)])
      upstream := upstream.set! index (rows.extract 1 rows.size)
    need (samples.all (fun row => row.all (·.size == 3)) && upstream.all (·.size == 3)) "block has missing paired rows"
    observations := observations.push { samples, upstream, initialRss }
  need ((← readLines (measured / "samples.jsonl")) == reconstructed) "combined samples differ from original paired process records"
  need ((← readLines (measured / "upstream.jsonl")) == upstreamReconstructed) "combined upstream samples differ from process records"
  return (freeze, observations)

def nsPerOp (sample : Json) : IO Float := do
  let elapsed ← number sample "elapsed_ns"
  let count ← number sample "operations"
  need (elapsed > 0 && count > 0) "zero time or operation count"
  return elapsed.toFloat / count.toFloat

def compactFloat (value : Float) : String :=
  toString ((value * 100).round / 100)

def analyzeSuite (build measured output : FilePath) : IO Unit := do
  fresh output
  analysisSelfCheck
  let (freeze, blocks) ← inspectMeasurement build measured
  let diagnostics ← readJson (measured / "diagnostics/diagnostics.json")
  let diagnosticBuildHash := digest (← IO.FS.readBinFile (build / "build.json"))
  need ((← strField diagnostics "status") == "passed" && (← strField diagnostics "build_blake3") ==
    diagnosticBuildHash) "diagnostics do not match the measured build"
  let gc ← field diagnostics "gc"
  need ((← strField gc "raw_blake3") == digest (← IO.FS.readBinFile (measured / "diagnostics/cakeml-gc.jsonl")))
    "retained collection diagnostics changed"
  let indices := bootstrapIndices
  let mut results := #[]
  let mut report := "# Native reversal: shared-host reference run\n\n"
  report := report ++ "This report covers one bounded reversal workload on one recorded x86-64 Linux host. " ++
    "It compares the checked Ix.Compiler object with consuming Lean and CakeML programs and the same arena C kernel compiled by CompCert, GCC, and Clang. " ++
    "The worker is pinned, but the host, SMT sibling, temperature, and turbo behavior are not controlled. These observations do not establish a dedicated regression baseline.\n\n" ++
    "Every row has 30 paired blocks in three sessions, with the median of three samples per executable per block. " ++
    "Samples accumulate at least 100 ms of measured work. Counts are identical across implementations in each paired case. " ++
    "The raw timer and handoff control is retained without subtraction. All valid slow observations are included. " ++
    "Intervals use 10,000 hierarchical paired bootstrap replicates (seed 2671931027), resampling sessions then blocks. " ++
    "Only three session clusters are available, so interval precision and generalization remain limited. Full medians, quartiles, intervals, session medians, and paired ratios are in `summary.json`.\n\n"
  for profile in [:2] do
    report := report ++ s!"## {if profile == 0 then "Entry plus bounded handoff" else "Fresh allocation lifecycle"}\n\n" ++
      "Nanoseconds per operation, median across block medians. Lifecycle includes construction, reversal, order-sensitive consumption, and normal memory management.\n\n" ++
      "| Length | Payload domain | Ix.Compiler | Lean | CakeML | CompCert | GCC | Clang |\n" ++
      "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |\n"
    for localId in [:19] do
      let id := profile * 19 + localId
      let specification := timingCases[id]!
      let mut implementationResults := #[]
      let mut blockValues := #[]
      for implementationIndex in [:6] do
        let values ← blocks.mapM fun block => do
          return median (← block.samples[id]![implementationIndex]!.mapM nsPerOp)
        blockValues := blockValues.push values
      for implementationIndex in [:6] do
        let values := blockValues[implementationIndex]!
        let stats := distribution indices values
        let ratios := values.zipWith (· / ·) blockValues[0]!
        let ratios := distribution indices ratios
        let ns := median values
        implementationResults := implementationResults.push (Json.mkObj [
          ("implementation", toJson implementations[implementationIndex]!), ("ns_per_operation", stats),
          ("ns_per_element", if specification.length == 0 then Json.null else toJson (ns / specification.length.toFloat)),
          ("operations_per_second", toJson (1000000000 / ns)),
          ("paired_speedup_baseline_over_compilatrix", ratios)])
      let domain := if specification.domain == 0 then "six patterns, <2^30" else
        ["", "2^63-1", "2^63", "2^64-1"][specification.domain]!
      report := report ++ s!"| {specification.length} | {domain} | " ++
        String.intercalate " | " ((blockValues.map (fun values => compactFloat (median values))).toList) ++ " |\n"
      results := results.push (Json.mkObj [("row", toJson id), ("length", toJson specification.length),
        ("domain", toJson specification.domain), ("profile", toJson (if profile == 0 then "entry+handoff" else "lifecycle")),
        ("implementations", Json.arr implementationResults)])
    report := report ++ "\n"
  report := report ++ "## Paired comparison at the current 64-element bound\n\n" ++
    "Each cell is baseline time / Ix.Compiler time, followed by its 95% interval. Values above one favor Ix.Compiler. " ++
    "The JSON summary retains paired intervals for every other length as well.\n\n" ++
    "| Profile | Domain | Lean | CakeML | CompCert | GCC | Clang |\n| --- | --- | --- | --- | --- | --- | --- |\n"
  for row in results do
    if (← number row "length") != 64 then continue
    let cells ← (← arrField row "implementations").extract 1 6 |>.mapM fun implementation => do
      let stats ← field implementation "paired_speedup_baseline_over_compilatrix"
      return s!"{compactFloat (← statistic stats "median")} [{compactFloat (← statistic stats "ci95_low")}, {compactFloat (← statistic stats "ci95_high")}]"
    report := report ++ s!"| {← strField row "profile"} | {domainName (← number row "domain")} | " ++ String.intercalate " | " cells.toList ++ " |\n"
  let mut memory := #[]
  report := report ++ "\n## Process memory and collection observations\n\n" ++
    "RSS is read from `/proc/self/statm`; peak RSS is the maximum recorded `getrusage(RUSAGE_SELF)` high-water value. " ++
    "Ready-process RSS includes initialized runtimes and immutable scalar datasets, before list work. " ++
    "These process measurements include allocator/runtime reservation and differ from live application bytes.\n\n" ++
    "| Implementation | Median ready RSS KiB | Minimum sample RSS KiB | Maximum sample RSS KiB | Maximum recorded peak KiB |\n| --- | ---: | ---: | ---: | ---: |\n"
  for index in [:6] do
    let initial := blocks.map fun block => block.initialRss[index]!.toFloat
    let mut rssMin : Option Nat := none
    let mut rssMax := 0
    let mut peak := 0
    for block in blocks do
      for row in block.samples do
        for sample in row[index]! do
          let rss ← number sample "rss_kb"
          rssMin := some (min rss (rssMin.getD rss))
          rssMax := max rss rssMax
          peak := max peak (← number sample "peak_rss_kb")
    memory := memory.push (Json.mkObj [("implementation", toJson implementations[index]!),
      ("ready_rss_kb_median", toJson (median initial)), ("minimum_sample_rss_kb", toJson rssMin),
      ("maximum_sample_rss_kb", toJson rssMax), ("maximum_recorded_peak_rss_kb", toJson peak)])
    report := report ++ s!"| {implementations[index]!} | {compactFloat (median initial)} | {rssMin.getD 0} | {rssMax} | {peak} |\n"
  let terminal ← field gc "terminal_collection"
  report := report ++ s!"\nThe separate CakeML lifecycle diagnostic observed {← number gc "natural_collections_in_sample_envelopes"} natural collections " ++
    s!"across 20 samples. Maximum observed post-collection live data was {← number gc "maximum_post_gc_live_bytes"} bytes; " ++
    s!"the separately timed terminal collection took {← number terminal "elapsed_ns"} ns and retained {← number terminal "post_gc_live_bytes"} bytes. " ++
    "These instrumented event counts include each sample envelope and are separate from primary timing. " ++
    s!"Hardware counters: {← strField (← field diagnostics "hardware_counters") "status"}; the diagnostic record gives the actual availability reason/event output.\n\n"
  report := report ++ "## Native code and compiler work\n\n" ++
    "The following object `.text` sizes come from retained `size -A` output. The CakeML object includes the ML driver and basis code; " ++
    "the Lean object includes its generated module entry, and the C/Ix.Compiler rows isolate the arena kernels. " ++
    "The complete sections, linked executable sizes, and dynamic dependencies are retained; these scopes are not interchangeable.\n\n" ++
    "| Object | `.text` bytes |\n| --- | ---: |\n"
  for entry in (← arrField diagnostics "code_sizes") do
    let name ← strField entry "name"
    if implementations.contains name then continue
    let text ← strField entry "gnu_size_A"
    let line := (text.splitOn "\n").find? (fun line => (words line).head? == some ".text")
    let count := line.bind (fun line => (words line)[1]?.bind String.toNat?)
    report := report ++ s!"| {name} | {count.map toString |>.getD "unavailable"} |\n"
  report := report ++ "\nCompiler rows are single observed process envelopes. They include process startup and the named producer/checker work; " ++
    "they are separate from seed installation, proof-library builds, and runtime comparisons. CPU time and peak compiler RSS are in the retained diagnostics.\n\n" ++
    "| Operation | Elapsed ms | Peak RSS KiB |\n| --- | ---: | ---: |\n"
  for cost in (← arrField diagnostics "compiler_costs") do
    let command ← field cost "command"
    let resources ← field cost "resources"
    report := report ++ s!"| {← strField cost "name"} | {compactFloat ((← number command "envelope_ns").toFloat / 1000000)} | {← number resources "peak_rss_kb"} |\n"
  report := report ++ "\n"
  let mut upstream := #[]
  report := report ++ "## Unchanged upstream computations\n\n" ++
    "These closed entries retain their native successor instructions and four direct calls. They take no runtime arguments. " ++
    "Their call timings are separate from the runtime-input reversal comparison.\n\n" ++
    "| Entry | Result | Native text bytes | Object bytes | Median ns/call | 95% interval |\n| --- | ---: | ---: | ---: | ---: | --- |\n"
  for index in [:2] do
    let name := if index == 0 then "applyClosed" else "letClosed"
    let values ← blocks.mapM fun block => do return median (← block.upstream[index]!.mapM nsPerOp)
    let stats := distribution indices values
    let native ← field (← readJson (build / s!"artifacts/upstream-{name}/upstream-{name}.json")) "native"
    let row := Json.mkObj [("name", toJson name), ("ns_per_call", stats), ("value", ← field native "value"),
      ("text_bytes", ← field native "text_bytes"), ("object_bytes", ← field native "object_bytes"),
      ("native_heap", ← field native "native_heap"), ("executions", ← field native "executions")]
    upstream := upstream.push row
    report := report ++ s!"| {name} | {← number native "value"} | {← number native "text_bytes"} | {← number native "object_bytes"} | " ++
      s!"{compactFloat (median values)} | {compactFloat (← statistic stats "ci95_low")}–{compactFloat (← statistic stats "ci95_high")} |\n"
  report := report ++ "\nThe baseline source/physical heap is fully reclaimed in the checked artifacts. Native Nat values use one exact 64-bit word and allocate no heap. " ++
    "The call traces write 48 bytes below the caller return slot. These closed translation-validation and supplied-state execution certificates do not close N3's open-call, branch/join, or F1's general stack contracts.\n\n" ++
    "Code sizes, compiler/checker resource envelopes, runtime dependencies, RSS observations, GC diagnostics, and complete inputs are retained with the build and raw run. " ++
    "Arena capacity is n+2 cells (80+32*(n+2) bytes); release clears cells before freeing the arena. " ++
    "Lean uniqueness diagnostics establish exclusive spines and cons reuse. CakeML uses a 64 MiB simple copying heap and an 8 MiB stack; separate diagnostics report actual collection cycles and terminal collection. " ++
    "Dropping roots is not immediate reclamation. Hardware counters are reported only when available.\n"
  let summary := Json.mkObj [("format", toJson "compilatrix/benchmark-analysis/1"),
    ("build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))) ,
    ("measurement_blake3", toJson (digest (← IO.FS.readBinFile (measured / "measurement.json")))),
    ("freeze_blake3", toJson (digest (← IO.FS.readBinFile (measured / "freeze.json")))),
    ("bootstrap", ← field freeze "bootstrap"), ("bootstrap_replicates", toJson (10000 : Nat)),
    ("bootstrap_seed", toJson (2671931027 : Nat)), ("quantile", toJson "linear interpolation at (n-1)*p"),
    ("within_block", toJson "median of three samples"), ("rows", Json.arr results), ("upstream", Json.arr upstream),
    ("process_memory", Json.arr memory), ("diagnostics", diagnostics),
    ("diagnostics_blake3", toJson (digest (← IO.FS.readBinFile (measured / "diagnostics/diagnostics.json")))),
    ("missing_rows", Json.arr #[]), ("failed_published_rows", Json.arr #[]), ("status", toJson "complete")]
  writeJson (output / "summary.json") summary
  IO.FS.writeFile (output / "report.md") report
  IO.println "benchmark analysis: 38 rows, paired uncertainty, two upstream entries, and complete raw-record replay passed"

end Benchmarks.Compiler
