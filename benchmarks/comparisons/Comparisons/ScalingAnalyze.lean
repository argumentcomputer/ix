import Comparisons.ScalingRun
import Comparisons.Analyze

namespace Benchmark.CompilerScaling
open Lean System Compilatrix.Tools.Check Compilatrix.Tools.UniqueCheck

def distribution (values : Array Float) : Json := Json.mkObj [
  ("samples", toJson values.size), ("minimum", toJson (quantile values 0 1)),
  ("q25", toJson (quantile values 1 4)), ("median", toJson (median values)),
  ("q75", toJson (quantile values 3 4)), ("maximum", toJson (quantile values 1 1))]

def stageValue (sample : Json) (name : String) : IO Nat := do
  let stages ← arrField (← field sample "metrics") "stages"
  match ← stages.findM? (fun stage => return (← strField stage "stage") == name) with
  | some stage => number stage "elapsed_ns"
  | none => return 0

/-- A sum of measured worker stages, not an estimate obtained by subtracting
diagnostic timings from the process envelope. Repeated checks stay separate. -/
def primaryTime (sample : Json) : IO Nat := do
  let stages ← arrField (← field sample "metrics") "stages"
  stages.foldlM (init := 0) fun total stage => do
    let name ← strField stage "stage"
    if name.startsWith "diagnostic-" || ["source-preflight", "hpt-certificate-check", "snapshot-decode-check"].contains name then return total
    return total + (← number stage "elapsed_ns")

def rowSummary (row : Json) (samples : Array Json) : IO Json := do
  let id ← strField row "id"
  let samples ← samples.filterM fun sample => return (← strField sample "id") == id
  need (!samples.isEmpty) "missing scaling row samples"
  let first ← arrField (← field samples[0]! "metrics") "stages"
  let mut stages := #[]
  for stage in first do
    let name ← strField stage "stage"
    let mut elapsed := #[]
    let mut peak := #[]
    let mut resident := #[]
    let mut nearTimer := 0
    for sample in samples do
      let metrics ← field sample "metrics"
      let actual ← present (← (← arrField metrics "stages").findM? fun row => return (← strField row "stage") == name) "stage disappeared"
      let ns ← number actual "elapsed_ns"
      elapsed := elapsed.push ns.toFloat
      peak := peak.push (← number (← field actual "memory_after") "process_peak_rss_kib").toFloat
      resident := resident.push (← number (← field actual "memory_after") "rss_kib").toFloat
      if ns < 100 * max 1 (← number metrics "timer_pair_min_ns") then nearTimer := nearTimer + 1
    stages := stages.push (Json.mkObj [("stage", toJson name), ("status", ← field stage "status"),
      ("elapsed_ns", distribution elapsed), ("process_peak_rss_kib", distribution peak), ("resident_rss_kib", distribution resident),
      ("samples_below_100_timer_pairs", toJson nearTimer)])
  return Json.mkObj [
    ("id", toJson id), ("case", ← field row "case"), ("mode", ← field row "mode"),
    ("outcome", ← field (← field row "reference") "outcome"), ("stages", Json.arr stages),
    ("primary_stage_sum_ns", distribution (← samples.mapM fun sample => return (← primaryTime sample).toFloat)),
    ("process_envelope_ns", distribution (← samples.mapM fun sample => return (← number (← field sample "process") "envelope_ns").toFloat)),
    ("process_peak_rss_kib", distribution (← samples.mapM fun sample => return (← number (← field sample "resources") "peak_rss_kb").toFloat))]

def paired (metadata : Json) (samples : Array Json) : IO (Array Json) := do
  let mut results := #[]
  for pair in ← arrField metadata "cache_pairs" do
    let coldId ← strField pair "cold"
    let warmId ← strField pair "warm"
    let cold ← samples.filterM fun sample => return (← strField sample "id") == coldId
    let mut ratios := #[]
    let mut primary := #[]
    let mut envelopes := #[]
    for sample in cold do
      let warm ← present (← samples.findM? fun other => return (← strField other "id") == warmId &&
        (← field other "session") == (← field sample "session") && (← field other "block") == (← field sample "block")) "missing paired cache sample"
      let coldTime := (← stageValue sample "cache-decode") + (← stageValue sample "hpt-cache-produce-check")
      let warmTime := (← stageValue warm "cache-decode") + (← stageValue warm "hpt-cache-produce-check")
      need (coldTime > 0 && warmTime > 0) "missing HPT cache stage"
      ratios := ratios.push (coldTime.toFloat / warmTime.toFloat)
      primary := primary.push ((← primaryTime sample).toFloat / (← primaryTime warm).toFloat)
      envelopes := envelopes.push ((← number (← field sample "process") "envelope_ns").toFloat /
        (← number (← field warm "process") "envelope_ns").toFloat)
    results := results.push (Json.mkObj [("cold", toJson coldId), ("warm", toJson warmId), ("reuse", ← field pair "reuse"),
      ("hpt_cold_over_warm", distribution ratios), ("primary_stage_sum_cold_over_warm", distribution primary),
      ("process_envelope_cold_over_warm", distribution envelopes)])
  return results

def shownNumber (value : Json) (key : String) : String :=
  match (value.getObjVal? key).toOption.bind (fun value => value.getNat?.toOption) with
  | none => "—"
  | some value => toString value

def shownTime (row : Json) (name : String) : IO String := do
  match ← (← arrField row "stages").findM? (fun stage => return (← strField stage "stage") == name) with
  | none => pure "—"
  | some stage => return compactFloat ((← statistic (← field stage "elapsed_ns") "median") / 1000000)

def analyzeSuite (build measured output : FilePath) : IO Unit := do
  fresh output
  let (metadata, samples) ← inspectMeasurement build measured
  let rows ← (← arrField metadata "rows").mapM (fun row => rowSummary row samples)
  let pairs ← paired metadata samples
  let profile ← strField metadata "profile"
  let freeze ← readJson (measured / "freeze.json")
  let mut report := "# Compiler scaling\n\n" ++
    s!"{rows.size} workload/cache rows; {sessions profile} consecutive sessions × {blocksPerSession profile} shuffled blocks. " ++
    "Each stage sample is one invocation in a fresh, pinned worker process. Tables show medians; the JSON retains quartiles, minima, maxima, and every stage. " ++
    "These are descriptive observations on a shared host, with no performance threshold or confidence claim.\n\n" ++
    "The source frontend includes address/usage checking, erasure, source certification, and IxIR₁ lowering. " ++
    "Separate coverage discovery/source certificate timings rerun that work. HPT certificate checking and snapshot ingestion also have separate replay timings. " ++
    "The primary-stage sum omits those repeated diagnostics and the preflight already included in the frontend; the process envelope includes all work and artifact IO. No timer or diagnostic cost is subtracted.\n\n" ++
    "Memory is process RSS and raw reported VmHWM at stage boundaries, including earlier phases, retained artifacts, diagnostics and IO; GNU time records the final process peak. " ++
    "It is not an isolated allocation count or per-phase incremental peak. ELF-less rows retain their exact rejection or requested endpoint. " ++
    "Source proof terms are erased; source database counts/work charges, HPT candidate JSON bytes, and canonical HPT store bytes are reported separately.\n\n"
  for family in ["declarations", "call-depth", "branches", "allocations", "candidates", "joins"] do
    report := report ++ s!"## {family}\n\n| Size | Result | Frontend ms | HPT ms | IxIR₂ ms | x86 encode/check ms | Process peak MiB | HPT store B | Snapshot B | ELF B |\n" ++
      "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n"
    for row in rows do
      let case ← checked (fromJson? (← field row "case") : Except String Case)
      if case.family != family || case.edited || (← strField row "mode") != "cold" then continue
      let outcome ← field row "outcome"
      let mut status ← strField outcome "status"
      if status == "rejected" then status := s!"reject: {← strField (← field outcome "rejection") "stage"}"
      let peak := (← statistic (← field row "process_peak_rss_kib") "maximum") / 1024
      report := report ++ s!"| {case.size} | {status} | {← shownTime row "source-to-ixir1"} | {← shownTime row "hpt-cache-produce-check"} | " ++
        s!"{← shownTime row "ixir2-lower-check"} | {← shownTime row "x86-encode-check"} | {compactFloat peak} | " ++
        s!"{shownNumber outcome "hpt_store_bytes"} | {shownNumber outcome "snapshot_bytes"} | {shownNumber outcome "elf_bytes"} |\n"
    report := report ++ "\n"
  report := report ++ "## Cache reuse\n\nCold/warm refer to absent/persisted HPT evidence, not the OS page cache. " ++
    "Warm processes decode the retained store and validate hits against the current addressed graph. Source certification runs again. " ++
    "The edit changes one leaf projection and readdresses dependent callers; its scalar result stays unchanged. Ratios are paired within each block; values above one favor the warm run.\n\n" ++
    "| Cold row | Hits | Rebuilt | HPT cold/warm median | Primary stages cold/warm | Process cold/warm |\n| --- | ---: | ---: | ---: | ---: | ---: |\n"
  for pair in pairs do
    let reuse ← field pair "reuse"
    report := report ++ s!"| {← strField pair "cold"} | {← number reuse "hits"} | {← number reuse "misses"} | " ++
      s!"{compactFloat (← statistic (← field pair "hpt_cold_over_warm") "median")} | " ++
      s!"{compactFloat (← statistic (← field pair "primary_stage_sum_cold_over_warm") "median")} | " ++
      s!"{compactFloat (← statistic (← field pair "process_envelope_cold_over_warm") "median")} |\n"
  report := report ++ "\n## Rejections and experiment endpoints\n\n"
  for row in rows do
    let mode ← strField row "mode"
    if mode == "warm" || mode == "edit-warm" then continue
    let outcome ← field row "outcome"
    let status ← strField outcome "status"
    if status == "rejected" then
      let rejection ← field outcome "rejection"
      report := report ++ s!"- `{← strField row "id"}` / `{← strField rejection "stage"}`: {(← strField rejection "reason").replace "\n" " "}\n"
    else if status == "lowered" then report := report ++ s!"- `{← strField row "id"}`: fixed experiment endpoint after native lowering; {shownNumber outcome "x86_blocks"} target blocks, {shownNumber outcome "x86_instructions"} instructions. No ELF timing or rejection is claimed.\n"
  report := report ++ "\nThe Ixon branch family has no converging joins. The supplementary join family starts from a checked IxIR₂ snapshot and has no source/HPT measurements. " ++
    "Full object emission stops at eight joins; larger cases measure selection/lowering and preserve its rejection boundary. Candidate fixtures isolate preflight admission only and do not claim successful source certification at 512 candidates.\n"
  report := report ++ "\nThe allocation reference matrix stops at size 128. Larger setup probes are retained separately: size 256 required about 21 seconds to construct its canonical input; size 512 hit the 120-second process CPU guard during construction. That setup failure is not a compiler rejection or a reference timing sample.\n"
  writeJson (output / "summary.json") (Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-analysis/1"), ("build_blake3", ← field freeze "build_blake3"),
    ("freeze_blake3", toJson (digest (← IO.FS.readBinFile (measured / "freeze.json")))), ("rows", Json.arr rows),
    ("cache_pairs", Json.arr pairs), ("statistics", toJson "descriptive across all samples; no confidence interval or timing threshold")])
  IO.FS.writeFile (output / "report.md") report
  IO.println s!"compiler scaling analysis: {samples.size} complete fresh-process samples"

end Benchmark.CompilerScaling
