import Benchmark.ScalingAnalyze
import Benchmark.Reproduce

namespace Benchmark.CompilerScaling
open Lean System Compilatrix.Tools.Check Compilatrix.Tools.UniqueCheck

def reproduceSuite (build measured output : FilePath) : IO Unit := do
  let build ← absolute build
  let measured ← absolute measured
  let output ← absolute output
  let (metadata, _) ← inspectMeasurement build measured
  fresh output
  let environment ← checked (fromJson? (← field metadata "build_environment") : Except String (Array (String × Option String)))
  need (environment.map Prod.fst == buildEnvNames) "recorded compiler environment inventory changed"
  for row in ← array (← readJson (build / "tool-identities.json")) do
    need (digest (← IO.FS.readBinFile (← strField row "resolved")) == (← strField row "blake3")) "installed replay tool differs from the retained identity"
  let snapshot ← readJson (build / "source.json")
  need (digest (← IO.FS.readBinFile (build / "source.tar.gz")) == (← strField snapshot "archive_blake3")) "compiler source archive digest changed"
  let inventory ← arrField snapshot "files"
  let names ← inventory.mapM (fun row => strField row "path")
  need (names.toList.Nodup && names.all (fun name => !name.startsWith "/" &&
    !(name.splitOn "/").any (fun part => part == ".." || part.isEmpty))) "unsafe compiler source archive inventory"
  let listing := (← run "tar" #["-tzf", (build / "source.tar.gz").toString]).trimAscii.toString.splitOn "\n"
  need (listing.mergeSort (· ≤ ·) == names.toList.mergeSort (· ≤ ·)) "compiler source tar inventory changed"
  let source := output / "source"
  IO.FS.createDirAll source
  let _ ← run "tar" #["--no-same-owner", "--no-same-permissions", "-xzf", (build / "source.tar.gz").toString, "-C", source.toString]
  for row in inventory do
    let bytes ← IO.FS.readBinFile (source / (← strField row "path"))
    need (bytes.size == (← number row "bytes") && digest bytes == (← strField row "blake3")) "extracted compiler source differs"
  IO.FS.createDirAll (source / ".lake/build/bin")
  for name in ["benchmark", "compiler-scaling"] do
    let _ ← run "cp" #[(build / "tools" / name).toString, (source / ".lake/build/bin" / name).toString]
  let runner := (source / ".lake/build/bin/benchmark").toString
  let rebuilt := output / "build"
  replayCommand source environment runner #["compiler-scaling-build", rebuilt.toString, "--profile", ← strField metadata "profile",
    "--gcc", ← strField metadata "gcc", "--time", ← strField metadata "timer_tool"] (output / "rebuild.jsonl")
  let replayed ← inspectBuild rebuilt
  for key in ["cases", "rows", "cache_pairs", "inputs", "tools", "harness", "protocol_blake3", "tool_identities_blake3"] do
    need ((← field replayed key) == (← field metadata key)) s!"fresh compiler replay changed {key}"
  replayCommand source environment runner #["compiler-scaling-verify", rebuilt.toString, (output / "correctness").toString]
    (output / "verify.jsonl")
  let original ← readJson (measured / "correctness.json")
  let checked ← readJson (output / "correctness/correctness.json")
  for key in ["cases", "cache_pairs", "regressions", "status"] do
    need ((← field original key) == (← field checked key)) s!"replayed compiler correctness changed {key}"
  replayCommand source environment runner #["compiler-scaling-analyze", build.toString, measured.toString, (output / "analysis").toString]
    (output / "analysis.jsonl")
  for file in ["summary.json", "report.md"] do
    need ((← IO.FS.readBinFile (output / "analysis" / file)) == (← IO.FS.readBinFile (measured / "analysis" / file))) s!"replayed compiler analysis changed {file}"
  writeJson (output / "reproduction.json") (Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-reproduction/1"), ("status", toJson "passed"),
    ("source_archive_blake3", ← field snapshot "archive_blake3"), ("source_files", toJson inventory.size),
    ("original_build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))),
    ("artifact_rows", toJson (← arrField metadata "rows").size), ("artifacts_exact", toJson true),
    ("correctness_exact", toJson true), ("analysis_exact", toJson true), ("timing_samples_rerun", toJson false),
    ("scope", toJson "fresh extracted source directory; empty environment plus recorded variables; retained hashed compiler/orchestrator binaries and pinned installed tools; compiler executable itself is not rebuilt from Lean")])
  IO.println "compiler scaling reproduction: exact artifacts, cache reuse, correctness and analysis from retained source and compiler seeds"

def smokeSuite (output : FilePath) (gcc : String := "gcc") (timer : String := "time") : IO Unit := do
  let output ← absolute output
  fresh output
  buildSuite (output / "build") "smoke" ".lake/build/bin/compiler-scaling" gcc timer
  verifySuite (output / "build") (output / "correctness")
  measureSuite (output / "build") (output / "correctness") (output / "measured") (← firstCore)
  analyzeSuite (output / "build") (output / "measured") (output / "measured/analysis")
  measurementRegressions (output / "build") (output / "measured") (output / "measurement-regressions")
  reproduceSuite (output / "build") (output / "measured") (output / "reproduced")

end Benchmark.CompilerScaling
