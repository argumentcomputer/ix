import Lake
open System Lake DSL

package aiur where
  version := v!"0.1.0"
  -- Preserve the elaboration of the verified 4.29 monadic definitions.
  leanOptions := #[
    ⟨`backward.do.legacy, true⟩,
    ⟨`weak.linter.constructorNameAsVariable, false⟩,
    ⟨`weak.linter.defProp, false⟩,
    ⟨`weak.linter.deprecated, false⟩,
    ⟨`weak.linter.style.haveILetI, false⟩,
    ⟨`weak.linter.unnecessarySeqFocus, false⟩,
    ⟨`weak.linter.unnecessarySimpa, false⟩,
    ⟨`weak.linter.unreachableTactic, false⟩,
    ⟨`weak.linter.unusedSectionVars, false⟩,
    ⟨`weak.linter.unusedSimpArgs, false⟩,
    ⟨`weak.linter.unusedTactic, false⟩,
    ⟨`weak.linter.unusedVariables, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.34.1"

/-- Keep ordinary Cargo builds independent of Lean. Only the Lean executable
link step needs this archive and the small C object-ABI adapter. -/
target aiur_rs pkg : FilePath := do
  let sources ← inputDir (pkg.dir / ".." / "crates" / "aiur" / "src") true (fun path => path.extension == some "rs")
  let manifests := Job.collectArray #[
    ← inputTextFile (pkg.dir / ".." / "crates" / "aiur" / "Cargo.toml"),
    ← inputTextFile (pkg.dir / ".." / "Cargo.toml"),
    ← inputTextFile (pkg.dir / ".." / "Cargo.lock"),
    ← inputTextFile (pkg.dir / ".." / "rust-toolchain.toml")]
  let deps := sources.zipWith (fun a b => (a,b)) manifests
  let output := pkg.staticLibDir / nameToStaticLib "aiur_rs"
  buildFileAfterDep output deps fun _ => do
    proc { cmd := "cargo", args := #["build", "--release", "-p", "aiur", "--lib", "--locked"], cwd := pkg.dir / ".." } (quiet := true)
    copyFile (pkg.dir / ".." / "target" / "release" / nameToStaticLib "aiur") output

target execution_o pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "c" / "execution.c")
  buildO (pkg.buildDir / "c" / "execution.o") source
    #["-I", (← getLeanIncludeDir).toString] #["-fPIC"] "cc" getLeanTrace

@[default_target]
lean_lib Aiur where
  globs := #[.andSubmodules `Aiur]

lean_lib AiurTests

@[test_driver]
lean_exe aiur_tests where
  root := `AiurTests
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe blake3_stats where
  root := `Examples.Blake3

lean_exe aiur_execution where
  root := `Examples.Execution
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe execution_tests where
  root := `Examples.ExecutionChecks
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe trace_tests where
  root := `Examples.TraceChecks
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe aiur_hints where
  root := `Examples.ExecutionHints
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe trie_export where
  root := `Examples.Trie

lean_exe u32_tests where
  root := `Examples.U32

lean_exe library_tests where
  root := `Examples.LibraryChecks

lean_exe grouping_example where
  root := `Examples.Grouping

/-- Writes or checks the depth-pass fixture `crates/aiur/tests/fixtures/depth.ixa`. -/
lean_exe depth_example where
  root := `Examples.Depth

lean_exe grouping_tune where
  root := `Examples.GroupingTune

/-- Searches for a function-grouping policy from `grouping_tune --metrics`
output and measured row counts (see `Examples/GroupingSearch.lean`). -/
lean_exe grouping_search where
  root := `Examples.GroupingSearch

lean_exe bn254_execution_fixture where
  root := `Examples.BN254Execution
lean_exe bn254_trace_fixture where
  root := `Examples.BN254Trace
lean_exe bn254_grouped_fixture where
  root := `Examples.BN254Grouped
lean_exe bn254_gap_fixture where
  root := `Examples.BN254Gap
lean_exe bn254_inactive_fixture where
  root := `Examples.BN254Inactive
lean_exe bn254_fq_fixture where
  root := `Examples.BN254Fq
lean_exe bn254_fq_relation_fixture where
  root := `Examples.BN254FqRelation
lean_exe bn254_g1_fixture where
  root := `Examples.BN254G1
lean_exe bn254_g1_encoding_fixture where
  root := `Examples.BN254G1Encoding
lean_exe bn254_fq_products_fixture where
  root := `Examples.BN254FqProducts
lean_exe bn254_pairing_fixture where
  root := `Examples.BN254Pairing
lean_exe bn254_preparation_check where
  root := `Examples.BN254Preparation
lean_exe emulated_goldilocks_fixture where
  root := `Examples.EmulatedGoldilocks
lean_exe wide_artifact_fixture where
  root := `Examples.WideArtifact
lean_exe table_uniqueness_checks where
  root := `Examples.TableUniqueness

/-- Fails if any declaration of the package uses an axiom beyond propext,
Classical.choice and Quot.sound. Run after `lake build aiur/Aiur`:
`lake env Aiur/.lake/build/bin/axiom_sweep Aiur`. -/
lean_exe axiom_sweep where
  root := `Examples.AxiomSweep

/-- Converts `.aiur` module source text to embedded `aiur⟦ … ⟧` Lean syntax,
checking that both lower to the same program (`Tools/AiurEmbed.lean`). -/
lean_exe aiur_embed where
  root := `Tools.AiurEmbed
  supportInterpreter := true

/- ix-ai-pipeline: the triage model's SGD step as a formal Aiur program (local worktree only). -/
lean_lib IxAICore

lean_lib IxAIStep

/- Refinement of `IxAIStep`'s `Fixed` program: its emitted definitions and path lemmas. -/
-- An explicit root: `IxAIRefine/Fixed/specgen` holds generator fragments that are not modules.
lean_lib IxAIRefine

lean_exe ixai_step where
  root := `IxAIStepMain
  moreLinkObjs := #[execution_o, aiur_rs]

/- The whole training run as one execution (`FixedTree::train_tree`) and its exporter. -/
lean_lib IxAITree

lean_exe ixai_tree where
  root := `IxAITreeMain
  moreLinkObjs := #[execution_o, aiur_rs]

/- ix-ai-pipeline: the GPU trainer. `IxAIGpuHost/cuda` holds the CUDA kernels (`step.cu`) and the
C shim giving them Lean's object ABI (`ixai_gpu.c`); the host is `IxAIGpuHost`. -/

/-- nvcc, as `crates/aiur/build.rs` finds it: `NVCC`, then `CUDA_HOME`/`CUDA_PATH`, then `PATH`,
resolved so that the toolkit's libraries are found next to it. -/
def nvccPath : IO FilePath := do
  if let some nvcc ← IO.getEnv "NVCC" then return nvcc
  for var in ["CUDA_HOME", "CUDA_PATH"] do
    if let some root ← IO.getEnv var then
      let candidate := FilePath.mk root / "bin" / "nvcc"
      if ← candidate.pathExists then return candidate
  if let some path ← IO.getEnv "PATH" then
    for dir in path.splitOn ":" do
      let candidate := FilePath.mk dir / "nvcc"
      if ← candidate.pathExists then return candidate
  return "nvcc"

/-- The CUDA architectures, as `crates/aiur/build.rs` selects them: `MULTI_STARK_CUDA_ARCHS`,
else the visible GPUs' compute capabilities, else sm_80. -/
def cudaArchs : IO (Array String) := do
  let configured ← match ← IO.getEnv "MULTI_STARK_CUDA_ARCHS" with
    | some archs => pure (archs.splitOn ",")
    | none =>
      try
        let out ← IO.Process.output
          { cmd := "nvidia-smi", args := #["--query-gpu=compute_cap", "--format=csv,noheader"] }
        pure (if out.exitCode == 0 then out.stdout.splitOn "\n" else [])
      catch _ => pure []
  let archs := configured.map (fun a => String.ofList (a.toList.filter Char.isDigit)) |>.filter (!·.isEmpty)
  let archs := archs.eraseDups.toArray.qsort (· < ·)
  return if archs.isEmpty then #["80"] else archs

target ixai_gpu_step_o pkg : FilePath := do
  let nvcc ← nvccPath
  let gencode := (← cudaArchs).map fun a => s!"-gencode=arch=compute_{a},code=sm_{a}"
  let source ← inputTextFile (pkg.dir / "IxAIGpuHost" / "cuda" / "step.cu")
  buildO (pkg.buildDir / "cuda" / "step.o") source #[]
    (#["--std=c++17", "--cudart=static", "--default-stream=per-thread", "-O3", "-lineinfo",
      "--compiler-options=-fPIC"] ++ gencode) nvcc

target ixai_gpu_shim_o pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "IxAIGpuHost" / "cuda" / "ixai_gpu.c")
  buildO (pkg.buildDir / "cuda" / "ixai_gpu.o") source
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc" getLeanTrace

/-- The static CUDA runtime, from the toolkit of `nvccPath` (`lib64`, else
`targets/x86_64-linux/lib`), as `crates/aiur/build.rs` links it. -/
target cudart_static : FilePath := do
  let some root := (← nvccPath).parent >>= (·.parent)
    | error "cannot locate the CUDA toolkit: set NVCC or CUDA_HOME"
  for dir in [root / "lib64", root / "targets" / "x86_64-linux" / "lib"] do
    let lib := dir / "libcudart_static.a"
    if ← lib.pathExists then return ← inputBinFile lib
  error s!"libcudart_static.a not found under {root}"

lean_lib IxAIGpu

lean_lib IxAIGpuHost where
  globs := #[.andSubmodules `IxAIGpuHost]

lean_exe ixai_gpu where
  root := `IxAIGpuMain
  moreLinkObjs := #[execution_o, aiur_rs, ixai_gpu_shim_o, ixai_gpu_step_o, cudart_static]
