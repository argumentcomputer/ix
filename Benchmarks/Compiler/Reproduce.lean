import Benchmarks.Compiler.Diagnostics

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def replayCommand (directory : FilePath) (environment : Array (String × Option String))
    (command : String) (arguments : Array String) (log : FilePath) : IO Unit := do
  let assignments := environment.filterMap fun (name, value) => value.map (fun value => s!"{name}={value}")
  let result ← streamed { cmd := "env", args := #["-i"] ++ assignments ++ #[command] ++ arguments, cwd := some directory } log
  IO.FS.writeFile (log.withExtension "stderr") result.stderr
  writeJson (log.withExtension "command.json") (Json.mkObj [("environment_policy", toJson "env -i plus the exact recorded build variables"),
    ("environment", toJson environment), ("cwd", toJson directory.toString), ("command", toJson command),
    ("arguments", toJson arguments), ("exit_code", toJson result.exitCode.toNat)])
  need (result.exitCode == 0) s!"independent environment command failed; see {log}: {result.stderr}"

def rebuildArtifacts (build output : FilePath) : IO FilePath := do
  let build ← absolute build
  let output ← absolute output
  fresh output
  let metadata ← inspectBuild build
  let environment ← checked (fromJson? (← field metadata "build_environment") : Except String (Array (String × Option String)))
  need (environment.map Prod.fst == buildEnvNames) "recorded build environment inventory disagrees"
  let toolIdentities ← array (← readJson (build / "tool-identities.json"))
  for row in toolIdentities do
    let original ← strField row "resolved"
    let path ← if (← strField row "name") == "cakeml" then
        pure (build / (← strField row "retained_path"))
      else pure (FilePath.mk original)
    need (digest (← IO.FS.readBinFile path) == (← strField row "blake3")) "installed tool differs from retained compiler seed"
  let snapshot ← readJson (build / "source.json")
  need (digest (← IO.FS.readBinFile (build / "source.tar.gz")) == (← strField snapshot "archive_blake3")) "source archive digest disagrees"
  let source := output / "source"
  IO.FS.createDirAll source
  let inventory ← arrField snapshot "files"
  let names ← inventory.mapM (fun row => strField row "path")
  need (names.toList.Nodup && names.all (fun name => !name.startsWith "/" &&
    !(name.splitOn "/").any (fun part => part == ".." || part.isEmpty))) "unsafe source archive inventory"
  let listing := (← run "tar" #["-tzf", (build / "source.tar.gz").toString]).trimAscii.toString.splitOn "\n"
  need (listing.mergeSort (· ≤ ·) == names.toList.mergeSort (· ≤ ·)) "source tar inventory disagrees"
  let _ ← run "tar" #["--no-same-owner", "--no-same-permissions", "-xzf", (build / "source.tar.gz").toString, "-C", source.toString]
  for row in inventory do
    let bytes ← IO.FS.readBinFile (source / (← strField row "path"))
    need (bytes.size == (← number row "bytes") && digest bytes == (← strField row "blake3")) "extracted source differs from retained snapshot"
  IO.FS.createDirAll (source / ".lake/build/bin")
  for path in (← files (build / "tools-bin")) do
    let _ ← run "cp" #[path.toString, (source / ".lake/build/bin" / path.fileName.getD "missing").toString]
  let runner := (source / ".lake/build/bin/compiler-benchmark").toString
  let recordedTools ← checked (fromJson? (← field metadata "tool_commands") : Except String Toolchains)
  let tools := { recordedTools with cakeml := (source / ".lake/build/bin/cakeml-bootstrap").toString }
  let rebuilt := output / "build"
  replayCommand source environment runner #["build", rebuilt.toString, "--gcc", tools.gcc, "--clang", tools.clang,
    "--compcert", tools.compcert, "--cakeml", tools.cakeml, "--time", tools.timerTool] (output / "rebuild.jsonl")
  let rebuiltMetadata ← inspectBuild rebuilt
  for key in ["artifacts", "executables", "tools", "datasets_blake3", "manifest_blake3", "toolchains_blake3"] do
    need ((← field rebuiltMetadata key) == (← field metadata key)) s!"independent rebuild changed {key}"
  writeJson (output / "rebuild-check.json") (Json.mkObj [("source_files", toJson inventory.size),
    ("source_archive_blake3", ← field snapshot "archive_blake3"), ("artifacts_exact", toJson true),
    ("executables_exact", toJson true), ("status", toJson "passed")])
  IO.println "benchmark rebuild check: fresh source/environment produced exact objects and executables"
  return source

def reproduceSuite (build measured output : FilePath) : IO Unit := do
  let build ← absolute build
  let measured ← absolute measured
  let output ← absolute output
  let (_, _) ← inspectMeasurement build measured
  let source ← rebuildArtifacts build output
  let metadata ← inspectBuild build
  let snapshot ← readJson (build / "source.json")
  let inventory ← arrField snapshot "files"
  let environment ← checked (fromJson? (← field metadata "build_environment") : Except String (Array (String × Option String)))
  let runner := (source / ".lake/build/bin/compiler-benchmark").toString
  let rebuilt := output / "build"
  replayCommand source environment runner #["verify", rebuilt.toString, (output / "correctness").toString] (output / "verify.jsonl")
  let originalCorrectness ← readJson (measured / "correctness.json")
  let replayCorrectness ← readJson (output / "correctness/correctness.json")
  let originalMatrices ← arrField originalCorrectness "matrices"
  let replayMatrices ← arrField replayCorrectness "matrices"
  need (originalMatrices.size == replayMatrices.size) "independent correctness inventory changed"
  for i in [:originalMatrices.size] do
    need ((← field originalMatrices[i]! "result") == (← field replayMatrices[i]! "result")) "independent complete matrix differs"
  -- Retained samples remain inputs. Reproduction never asks clock readings
  -- or diagnostic compiler resource envelopes to be byte-identical.
  replayCommand source environment runner #["analyze", build.toString, measured.toString, (output / "analysis").toString]
    (output / "analysis.jsonl")
  for file in ["summary.json", "report.md"] do
    need ((← IO.FS.readBinFile (output / "analysis" / file)) == (← IO.FS.readBinFile (measured / "analysis" / file)))
      s!"independent analysis changed {file}"
  writeJson (output / "reproduction.json") (Json.mkObj [("format", toJson "compilatrix/benchmark-reproduction/1"),
    ("source_archive_blake3", ← field snapshot "archive_blake3"), ("original_build_blake3", toJson (digest (← IO.FS.readBinFile (build / "build.json")))),
    ("rebuilt_build_blake3", toJson (digest (← IO.FS.readBinFile (rebuilt / "build.json")))),
    ("source_files", toJson inventory.size), ("artifacts_exact", toJson true), ("executables_exact", toJson true),
    ("correctness_exact", toJson true), ("analysis_exact", toJson true),
    ("scope", toJson "fresh extracted source directory and empty process environment; retained hashed compiler/checker seeds; same physical host and pinned Nix runtime closure"),
    ("timing_samples_rerun", toJson false), ("status", toJson "passed")])
  IO.println "benchmark reproduction: clean source/environment rebuild, exact objects/executables, complete correctness, and byte-exact analysis passed"

end Benchmarks.Compiler
