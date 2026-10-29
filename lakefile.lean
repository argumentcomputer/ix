import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"
  moreLinkObjs := #[⟨.packageTarget .anonymous `ix_cuda_runtime⟩]
  -- The CUDA DSO resolves libc against the running system. Lean's link-time
  -- glibc stubs can be older; the DSO itself is linked with -z defs.
  moreLinkArgs := if System.Platform.isLinux then
    #["-Wl,--allow-shlib-undefined", "-Wl,-rpath,$ORIGIN/../lib"] else #[]

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "d8eb3e0d9a8e33fc116e6700df0418a1d8114508"

/- The pinned package supplies the pure Lean hash and host C/Rust
accelerators. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "3f8b805614a0bae1c033469ff893a8f0ee85f601"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.34.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.34.0"

require «ix-kernel» from "IxC" with
  if (get_config? profile).isSome then
    ({} : Lean.NameMap String).insert `profile ""
  else {}

/-! ## FFI

The Rust static libraries use `target` + `moreLinkObjs` instead of `extern_lib` because different Lean executables need different Cargo features:

- `ix` uses `ix_rs_net` (`parallel,net`) for networking support (iroh).
- `IxTests` uses `ix_rs_test` (`parallel,test-ffi`) for test-only FFI code.
- Other application targets inherit `ix_rs` (`parallel`, plus opt-in `cuda`)
  from the `Ix` `lean_lib`.

Compression runs inside `ix`. Its terminal backends (`plonk`, `groth16`) are
compiled into `ix_rs_net` only, so other executables never build Go. With
`cuda`, the native libraries (multi-stark's, the BN254 KZG/PLONK library and,
for Groth16, ICICLE) are copied to `.lake/build/lib` and found through
`$ORIGIN/../lib`.

The `ix_rs_test` and `ix_rs_net` targets fetch `ix_rs` first to guarantee ordering
before Cargo overwrites its release archive, then snapshot distinct Lake artifacts.
The second Cargo build is incremental — only feature-affected crates recompile.

The archives are built when native targets need them. Keeping Rust linkage on
`Ix` keeps `ix_rs` out of the certified kernel's build.
-/
section FFI

/-- `1`/`true`/`yes` or `0`/`false`/`no`; `default` when unset or empty. -/
def envFlag (name : String) (default : Bool) : IO Bool := do
  match ← IO.getEnv name with
  | none | some "" => pure default
  | some "1" | some "true" | some "yes" => pure true
  | some "0" | some "false" | some "no" => pure false
  | some _ => throw <| IO.userError s!"{name} must be 0/1, false/true or no/yes"

/-- Terminal backends of `ix`'s compression, mirroring the Cargo features of the
same names: `IX_PLONK` and `IX_GROTH16`, both off by default, so compression
ends at the recursive KZG proof. With `IX_CUDA`, each also enables its GPU
backend; Groth16 links an installed ICICLE library. -/
def compressionFeatures : IO (Array String) := do
  let mut features := #[]
  if ← envFlag "IX_PLONK" false then features := features.push "plonk"
  if ← envFlag "IX_GROTH16" false then features := features.push "groth16"
  return features

/-- Rust feature selection shared by compilation and native runtime linkage. -/
def cargoFeatures (testFfi : Bool := false) (net : Bool := false) : IO (Array String) := do
  -- IX_NO_PAR=1 disables parallel; IX_CUDA=1/true/yes enables CUDA;
  -- IX_CUDA_TRACE_CODEGEN=1 enables generated trace kernels and implies CUDA.
  let ixNoPar ← IO.getEnv "IX_NO_PAR"
  let ixCuda ← IO.getEnv "IX_CUDA"
  let ixTraceCodegen ← IO.getEnv "IX_CUDA_TRACE_CODEGEN"
  let mut features ← if net then compressionFeatures else pure #[]
  if ixNoPar != some "1" then features := features.push "parallel"
  if ixCuda == some "1" || ixCuda == some "true" || ixCuda == some "yes" then
    features := features.push "cuda"
  if ixTraceCodegen == some "1" || ixTraceCodegen == some "true" || ixTraceCodegen == some "yes" then
    features := features.push "cuda-trace-codegen"
  if net && !System.Platform.isOSX then features := features.push "net"
  if testFfi then features := features.push "test-ffi"
  return features

/-- Build args for `cargo build --release` with opt-in feature overrides.
Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) (net : Bool := false) : IO (Array String) := do
  let features ← cargoFeatures testFfi net
  IO.println s!"Ix Rust features: {if features.isEmpty then "none" else ",".intercalate features.toList}"
  let buildArgs := #["build", "--release", "--no-default-features", "-p", "ix-ffi"]
  if features.isEmpty then return buildArgs
  else return buildArgs ++ #["--features", ",".intercalate features.toList]

/-- Environment for every Cargo build here. Lean's bundled toolchain links
against glibc stubs older than 2.38, whose headers in C23 mode, the default
of recent GCC, redirect `strtol` and its relatives to `__isoc23_*` symbols
the stubs lack; compiling every C unit as C17 keeps the symbols the link
can resolve. `CFLAGS` already in the environment are kept. -/
def cargoEnvironment (environment : Array (String × Option String)) :
    Array (String × Option String) :=
  let existing := ((environment.find? (·.1 == "CFLAGS")).bind (·.2)).getD ""
  let cflags := if existing.isEmpty then "-std=gnu17" else s!"{existing} -std=gnu17"
  #[("CFLAGS", some cflags)]

/-- The native toolchain settings that change what Cargo produces. -/
def nativeToolchainVariables : Array String :=
  #["CFLAGS", "NVCC", "CUDA_HOME", "CUDA_PATH", "NVCC_CCBIN",
    "NVCC_PREPEND_FLAGS", "NVCC_APPEND_FLAGS", "MULTI_STARK_CUDA_ARCHS",
    "IX_KZG_CUDA_ARCHS", "GO", "CC", "CXX", "CGO_CFLAGS", "CGO_LDFLAGS",
    "IX_GROTH16_ICICLE_ROOT"]

def usesCuda (features : Array String) : Bool :=
  features.any fun feature => (feature.splitOn ",").any fun name =>
    name == "cuda" || name == "cuda-trace-codegen"

def cudaLibraryName := "libmulti_stark_cuda.so"
def bn254LibraryName := "libix_bn254_cuda.so"

/-- Cargo reports native build outputs even when the build is already fresh. -/
def cargoCudaLibrary (messages : String) : Except String FilePath := do
  for line in messages.splitOn "\n" do
    let .ok message := Lean.Json.parse line | continue
    let .ok libs := message.getObjValAs? (Array String) "linked_libs" | continue
    if libs.contains "dylib=multi_stark_cuda" then
      let directory ← message.getObjValAs? String "out_dir"
      return System.FilePath.mk directory / cudaLibraryName
  throw "Cargo did not report multi-stark's CUDA shared library"

def icicleLibraries : Array String :=
  #["libicicle_device.so", "libicicle_field_bn254.so", "libicicle_curve_bn254.so",
    "backend/cuda/libicicle_backend_cuda_device.so",
    "backend/bn254/cuda/libicicle_backend_cuda_field_bn254.so",
    "backend/bn254/cuda/libicicle_backend_cuda_curve_bn254.so"]

/-- The other native files the build scripts report: each `source` is copied to
`lib/<path>`, keeping ICICLE's backend plugins at the relative paths it loads
them from. -/
def cargoRuntimeArtifacts (messages : String) : Except String (Array (FilePath × String)) := do
  let mut artifacts := #[]
  for line in messages.splitOn "\n" do
    let .ok message := Lean.Json.parse line | continue
    let .ok variables := message.getObjValAs? (Array (Array String)) "env" | continue
    for entry in variables do
      if entry.size == 2 && entry[0]! == "IX_RUNTIME_ARTIFACTS" then
        let entries ← (← Lean.Json.parse entry[1]!).getArr?
        for artifact in entries do
          artifacts := artifacts.push
            (FilePath.mk (← artifact.getObjValAs? String "source"), ← artifact.getObjValAs? String "path")
  return artifacts

/-- Native libraries `features` load at runtime, relative to `lib/`; the
executables link the top-level ones. -/
def runtimeLibraries (features : Array String) : Array String :=
  if !usesCuda features then #[] else
  let groth16 := features.any fun feature => (feature.splitOn ",").contains "groth16"
  #[cudaLibraryName, bn254LibraryName] ++ (if groth16 then icicleLibraries else #[])

local instance : CheckExists (Array FilePath) where
  checkExists paths := paths.allM (·.pathExists)

local instance : GetMTime (Array FilePath) where
  getMTime paths := do
    paths.foldlM (fun oldest path => return min oldest (← getMTime path))
      (← getMTime paths[0]!)

/-- The installed ICICLE prefix, shared with Cargo's Groth16 build configuration. -/
def icicleRoot : BaseIO FilePath := do
  match ← IO.getEnv "IX_GROTH16_ICICLE_ROOT" with
  | none | some "" => return "/usr/local"
  | some path => return FilePath.mk path

/-- Replacing the inode keeps an already-loaded shared library intact. -/
def copyNativeArtifact (source output : FilePath) (tag : String) : JobM Unit := do
  IO.FS.createDirAll output.parent.get!
  let temporary := output.addExtension s!"{tag}.tmp"
  proc { cmd := "cp", args := #["-f", source.toString, temporary.toString] } (quiet := true)
  IO.FS.rename temporary output

/-- Every source, kernel, manifest and fixture file the Cargo builds read. -/
def rustSources (pkg : Package) : SpawnM (Job Unit) := do
  let sources ← inputDir (pkg.dir / "crates") true fun path =>
    path.extension == some "rs" || path.extension == some "cu" ||
    path.extension == some "cuh" || path.extension == some "cpp" ||
    path.extension == some "h" ||
    path.extension == some "hpp" || path.fileName == "Cargo.toml" ||
    path.fileName == "trace-manifest.json"
  let fixtures ← inputDir (pkg.dir / "crates/proof-compression/tests/fixtures") false fun path =>
    path.extension == some "bin"
  let manifests := Job.collectArray #[
    ← inputTextFile (pkg.dir / "Cargo.toml"),
    ← inputTextFile (pkg.dir / "Cargo.lock"),
    ← inputTextFile (pkg.dir / ".cargo/config.toml")
  ]
  let verifyingKeys ← inputDir (pkg.dir / "crates/proof-compression/verifying-keys") false fun path =>
    path.extension == some "json" || path.extension == some "bin"
  let sources := sources.zipWith (fun _ _ => ()) fixtures
  let sources := sources.zipWith (fun _ _ => ()) verifyingKeys
  return sources.zipWith (fun _ _ => ()) manifests

/-- Cargo's archive or executable and its native library are one build output.
Both must exist before a cached result can be used. -/
def buildCargoArtifact (pkg : Package) (args : Array String) (tag : String)
    (built output : FilePath) (before : Option (Job FilePath) := none) :
    FetchM (Job FilePath) := do
  let mut deps ← rustSources pkg
  let plonk := args.any fun argument => (argument.splitOn ",").contains "plonk"
  let groth16 := args.any fun argument => (argument.splitOn ",").contains "groth16"
  let gnark := plonk || groth16
  let groth16Cuda := groth16 && usesCuda args
  if gnark then
    let go ← inputDir (pkg.dir / "tools/plonk-wrapper") false fun path =>
      #["go", "h", "json", "bin"].contains (path.extension.getD "") ||
      path.fileName == "go.mod" || path.fileName == "go.sum"
    deps := deps.zipWith (fun _ _ => ()) go
  let icicle ← if groth16Cuda then do
    let root ← icicleRoot
    pure (some (pkg.dir / "crates/proof-compression" / root))
  else pure none
  if let some root := icicle then
    for name in icicleLibraries do
      let library := root / "lib" / name
      unless ← library.pathExists do
        error s!"Missing ICICLE library {library}. Install the pinned BN254 ICICLE libraries under /usr/local or set IX_GROTH16_ICICLE_ROOT to their installation prefix."
      deps := deps.zipWith (fun _ _ => ()) (← inputBinFile library)
  let orderedDeps := match before with
    | some before => deps.zipWith (fun _ _ => ()) before
    | none => deps
  let environment ← nativeToolchainVariables.mapM fun name => return (name, ← IO.getEnv name)
  let mut cargoEnv := cargoEnvironment environment
  if let some root := icicle then
    cargoEnv := cargoEnv.push ("IX_GROTH16_ICICLE_ROOT", some root.toString)
  let native := pkg.buildDir / "lib" / cudaLibraryName
  let cuda := usesCuda args
  let outputs := #[output] ++
    (runtimeLibraries args).map (pkg.buildDir / "lib" / FilePath.mk ·)
  orderedDeps.mapM fun _ => do
    let cargoEnv ← if gnark then do
      let go := (← IO.getEnv "GO").getD "go"
      let version ← captureProc' {
        cmd := go, args := #["version"], env := #[("GOTOOLCHAIN", some "local")]
      }
      pure <| cargoEnv.push ("IX_GNARK_GO_VERSION", some version.stdout)
    else pure cargoEnv
    addPureTrace (args, environment, cargoEnv) s!"cargo args: {args}; native toolchain: {environment}"
    buildUnlessUpToDate outputs (← getTrace) (output.addExtension "trace") do
      let result ← captureProc' {
        cmd := "cargo"
        args := args.push "--message-format=json-render-diagnostics"
        cwd := pkg.dir
        env := cargoEnv
      }
      unless result.stderr.isEmpty do logVerbose result.stderr
      if cuda then
        let source ← match cargoCudaLibrary result.stdout with
          | .ok source => pure source
          | .error message => error message
        copyNativeArtifact source native tag
      let artifacts ← match cargoRuntimeArtifacts result.stdout with
        | .ok artifacts => pure artifacts
        | .error message => error message
      for (source, path) in artifacts do
        copyNativeArtifact source (pkg.buildDir / "lib" / FilePath.mk path) tag
      copyNativeArtifact built output tag
    setTrace (← computeTrace outputs)
    return output

def buildRustStatic (pkg : Package) (args : Array String) (tag : String)
    (before : Option (Job FilePath) := none) : FetchM (Job FilePath) :=
  buildCargoArtifact pkg args tag
    (pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi")
    (pkg.buildDir / "lib" / s!"libix_ffi_{tag}.a") before

/-- Build the Rust static lib with default features (`parallel`). -/
target ix_rs pkg : FilePath := do
  buildRustStatic pkg (← cargoArgs) "default"

/-- An `ld` script naming the top-level native libraries in `libraries`, or an
empty archive when there are none. -/
def linkRuntime (pkg : Package) (name : String) (libraries : Array String)
    (after : Job FilePath) : SpawnM (Job FilePath) := do
  let libraries := libraries.filter (!·.contains '/')
  if libraries.isEmpty then
    return ← buildStaticLib (pkg.buildDir / "lib" / s!"lib{name}.a") #[]
  after.mapM fun _ => do
    let ldScript := pkg.buildDir / "lib" / s!"lib{name}.so"
    let paths := libraries.map fun (library : String) => (pkg.buildDir / "lib" / FilePath.mk library).toString
    IO.FS.writeFile ldScript s!"INPUT({" ".intercalate paths.toList})\n"
    setTrace (← computeTrace ldScript)
    return ldScript

/-- multi-stark's and the BN254 library, which every CUDA executable links. -/
target ix_cuda_runtime pkg : FilePath := do
  linkRuntime pkg "ix_cuda_runtime" (runtimeLibraries (← cargoFeatures)) (← ix_rs.fetch)

/-- Cargo feature variants wait for the default archive before building. -/
target ix_rs_test pkg : FilePath := do
  buildRustStatic pkg (← cargoArgs (testFfi := true)) "test" (some (← ix_rs.fetch))

/-- Build the Rust static lib with `net` for the `ix` CLI. -/
target ix_rs_net pkg : FilePath := do
  buildRustStatic pkg (← cargoArgs (net := true)) "net" (some (← ix_rs.fetch))

/-- ICICLE, which only `ix` links, when it compresses to Groth16 on CUDA. -/
target ix_terminal_runtime pkg : FilePath := do
  let all := runtimeLibraries (← cargoFeatures (net := true))
  let shared := runtimeLibraries (← cargoFeatures)
  linkRuntime pkg "ix_terminal_runtime" (all.filter (!shared.contains ·)) (← ix_rs_net.fetch)

end FFI

lean_lib MultiStark where
  moreLinkObjs := #[ix_rs]

/-- `lake -R -Kprofile build` compiles with frame pointers, so `perf` can unwind
call graphs through generated C (LBR and DWARF unwinding are unavailable on
the benchmark machines). The default build is unaffected. -/
def profileLeancArgs : Array String :=
  if (get_config? profile).isSome then #["-fno-omit-frame-pointer"] else #[]

/-- The main library, with Lake's default roots: every `Ix.*` module. Nothing the
`ix-kernel` dependency or `IxSharingVerify` owns is under the `Ix.` module root
(their declaration namespaces are, their module names are not), so this
library never shadows them. Keep new modules of theirs under their roots. -/
@[default_target]
lean_lib Ix where
  moreLinkObjs := #[ix_rs]
  moreLeancArgs := profileLeancArgs
  -- disabled because it breaks the binary
  --precompileModules := true

lean_exe ix where
  root := `Main
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_net, ix_terminal_runtime]

section Tests

lean_lib Tests

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true
  needs := #[`@/ix]
  moreLinkObjs := #[ix_rs_test]

lean_exe «arena-exclude» where
  root := `Tests.Ix.Kernel.ArenaExclude
  supportInterpreter := true

/-- Regenerates, or with `--check` verifies, the trace-codegen test fixtures:
the Rust writers, CUDA units and manifest the `aiur` parity tests compile
against. -/
lean_exe «trace-fixtures» where
  root := `Tests.Aiur.TraceFixtures
  supportInterpreter := true

/-- Compression CLI and stored-proof identity checks. -/
lean_exe «compression-cli-tests» where
  root := `Tests.CompressionCliMain
  needs := #[`@/ix]
  moreLinkObjs := #[ix_rs]

/-- Focused source-contract checks, including fresh-module registration export. -/
lean_exe «source-contract-tests» where
  root := `Tests.SourceContractMain
  supportInterpreter := true

/-- Focused Ixon v4 codec, locality, and cross-language transport checks;
`--export-fixtures` and `--export-handoff` regenerate the generated fixtures.
Scratch files live in `$IX_IXON_V4_DIR` (default `/tmp`); see `--help`. -/
lean_exe «ixon-v4-tests» where
  root := `Tests.IxonV4Main
  moreLinkObjs := #[ix_rs_test]

/-- Regenerate format-specific primitive identities from the installed Lean
environment, into `$IX_IXON_V4_DIR` (default `/tmp`); see `--help`. -/
lean_exe «ixon-v4-primitives» where
  root := `Tests.IxonV4Primitives
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_test]

end Tests

section Benchmarks

lean_exe «uniform-hard» where
  root := `Benchmarks.UniformHard

lean_exe «bench-aiur» where
  root := `Benchmarks.Aiur

lean_exe «bench-blake3» where
  root := `Benchmarks.Blake3

lean_exe «bench-sha256» where
  root := `Benchmarks.Sha256

lean_exe «bench-ixvm» where
  root := `Benchmarks.IxVM
  supportInterpreter := true

lean_exe «bench-shardmap» where
  root := `Benchmarks.ShardMap

lean_exe «bench-typecheck» where
  root := `Benchmarks.Typecheck
  supportInterpreter := true

lean_exe «bench-recursion-debug» where
  root := `Benchmarks.RecursionDebug
  supportInterpreter := true

lean_exe «bench-aggregate-policy» where
  root := `Benchmarks.AggregatePolicy
  supportInterpreter := true
  -- Keep ix_ffi ahead of Blake3's Rust staticlib. Importing the converged
  -- aggregator makes both archives direct dependencies; Rust allocator
  -- symbols are then resolved from ix_ffi and not pulled twice.
  moreLinkObjs := #[ix_rs]

lean_exe «bench-compile-init» where
  root := `Benchmarks.CompileInit

lean_exe «lean-sharing-prof» where
  root := `Benchmarks.LeanSharingProf

/-- Corpus measurement for canonical sharing (`docs/sharing-minimum.md`):
expands every stored sharing table in an `.ixe`, checks the production
rebuild and reports subterm, candidate and MSS statistics. -/
lean_exe «sharing-study» where
  root := `Benchmarks.SharingStudy

/- Typed TruthMines corpus records: the package catalog, the frozen admission
spec, fail-closed validation (elaboration-time `run_cmd` gate), and workspace
projections consumed by the `truthmines` driver and the `truthmines-spec`
suite. Pure data and pure functions; the nested corpus workspace they project
lives in `Benchmarks/TruthMines/`. -/
lean_lib TruthMinesSpec where
  globs := #[.submodules `Benchmarks.TruthMinesSpec]

/- The corpus driver: `gen [--check]` projects `Benchmarks/TruthMines/`
(lakefile, toolchain, per-member `Drivers/<Q>.lean`) from the typed
records, `spec` prints the member/driver table, and `build` compiles
per-member pieces (`pieces/<Q>.ixe`, one watchdogged `ix compile`
process each) and assembles + verifies the `truthmines.ixc` catalog
manifest. Needs `lake build ix` first for the `build` verb. -/
lean_exe truthmines where
  root := `Benchmarks.TruthMinesSpec.Main

end Benchmarks

section IxApplications

lean_lib Apps

lean_exe Apps.ZKVoting.Prover where
  supportInterpreter := true
lean_exe Apps.ZKVoting.Verifier

end IxApplications

section Scripts

open IO in
script install := do
  println! "Building ix"
  let out ← Process.output { cmd := "lake", args := #["build", "ix"]}
  if out.exitCode ≠ 0 then
    eprintln out.stderr; return out.exitCode

  -- Get the target directory for the ix binary
  let binDir ← match ← getEnv "HOME" with
    | some homeDir =>
      let binDir : FilePath := homeDir / ".local" / "bin"
      print s!"Target directory for the ix binary? (default={binDir}) "
      let input := (← (← getStdin).getLine).trimAscii.toString
      pure $ if input.isEmpty then binDir else ⟨input⟩
    | none =>
      print s!"Target directory for the ix binary? "
      let input := (← (← getStdin).getLine).trimAscii.toString
      if input.isEmpty then
        eprintln "Target directory can't be empty."; return 1
      pure ⟨input⟩

  let fullAccess := { read := true, write := true, execution := true }
  let noWriteAccess := { fullAccess with write := false }
  let fileRight := { user := fullAccess, group := fullAccess, other := noWriteAccess }
  FS.createDirAll binDir
  let destination := binDir / "ix"
  FS.writeBinFile destination (← FS.readBinFile $ ".lake" / "build" / "bin" / "ix")
  setAccessRights destination fileRight
  let libraryDir := binDir.parent.getD "." / "lib"
  for name in runtimeLibraries (← cargoFeatures (net := true)) do
    FS.createDirAll (libraryDir / name).parent.get!
    FS.writeBinFile (libraryDir / name) (← FS.readBinFile $ ".lake" / "build" / "lib" / name)
  return 0

script "get-exe-targets" := do
  let pkg ← getRootPackage
  let exeTargets := pkg.configTargets LeanExe.configKind
  for tgt in exeTargets do
    IO.println <| tgt.name.toString |>.dropPrefix "«" |>.dropSuffix "»" |>.toString
  return 0

@[lint_driver]
script "build-all" (args) := do
  let pkg ← getRootPackage
  let libNames := pkg.configTargets LeanLib.configKind |>.map (·.name.toString)
  let exeNames := pkg.configTargets LeanExe.configKind |>.map (·.name.toString)
  let allNames := (libNames ++ exeNames).toList
  let mut failed : Array String := #[]
  for name in allNames do
    IO.println s!"Building: {name}"
    let child ← IO.Process.spawn {
      cmd := "lake", args := #["build", name] ++ args
      stdout := .inherit, stderr := .inherit }
    let exitCode ← child.wait
    if exitCode != 0 then failed := failed.push name
  if failed.isEmpty then return 0
  IO.eprintln s!"Failed to build {failed.size} of {allNames.length} targets: {", ".intercalate failed.toList}"
  return 1

end Scripts

section IxSharingVerify

/- Proofs of the canonical sharing construction (`Ix.Sharing.Exact`) and their
audits: `IxSharingVerify` and every module under `IxSharingVerify/`, declaring
the `Ix.Sharing.Verify` namespace. Not a default target; `lake lint` builds
it. The module root is outside `Ix.` so that `Ix` never owns these modules.
The runtime modules under `Ix.Sharing.Exact` belong to `Ix`. -/
lean_lib IxSharingVerify where
  roots := #[`IxSharingVerify]
  globs := #[.andSubmodules `IxSharingVerify]

end IxSharingVerify

section IxC

/- The `ix-kernel` dependency owns the certified modules and their artifacts.
`lake -d IxC build --wfail` checks them without host dependencies;
the host tests below consume that same package. See `docs/kernel.md`. -/

/-- The kernel's fences, derived from con-leche's (`Tests/Ix/Kernel/{Layering,
TrustSurface}.lean`, over the layout of `Tests/Ix/Kernel/KernelLayout.lean`):
import layering, and the per-file escape allowlist with the lexer's self-test
on `Tests/Fixtures/trust-surface/lexer.lean`. Run from the repository root. -/
lean_exe «kernel-layering» where
  root := `Tests.Ix.Kernel.Layering

lean_exe «kernel-trust-surface» where
  root := `Tests.Ix.Kernel.TrustSurface

lean_exe «kernel-codec» where
  root := `Tests.Ix.Kernel.CodecHost
  moreLinkObjs := #[ix_rs_test]

lean_exe «kernel-order» where
  root := `Tests.Ix.Kernel.BlockOrderHost
  moreLinkObjs := #[ix_rs_test]

/-- Host-compiled Lean declarations through the certified entry
`Ix.Kernel.Admission.checkBytes`, each with an exact expected verdict. -/
lean_exe «kernel-entry-cases» where
  root := `Tests.Ix.Kernel.EntryCases
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- The kernel's universe-level comparison (`Level.leq`, `Level.isEquiv`, and
its Géran fallback `Level.Geran.leq`) against brute-force evaluation, on
random levels and on Ixon's canonical forms. -/
lean_exe «kernel-level-comparison» where
  root := `Tests.Ix.Kernel.LevelComparison
  moreLinkObjs := #[ix_rs]

/-- The Ixon reader against a direct translation of Lean's constants over
`Init` and `Std` (`Tests/Ix/Kernel/ReaderFidelity.lean`): the compiled environment
(`kernel-reader-fidelity .lake/envs/initstd.ixe [limit]`), `Init` and `Std`
compiled in process (`--compile [limit]`), `check-kernel`'s run
(`--check-kernel`) or the `lake test` fixture (`--fixture`). -/
lean_exe «kernel-reader-fidelity» where
  root := `Tests.Ix.Kernel.ReaderFidelityMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- The certified checker's benchmark drivers and reporting helpers. -/
lean_lib KernelEntry where
  roots := #[`Benchmarks.Kernel.CheckIxeStep,
    `Benchmarks.Kernel.CheckIxeReadCache, `Benchmarks.Kernel.CheckIxeStream, `Benchmarks.Kernel.CheckIxePool,
    `Benchmarks.Kernel.CheckIxe, `Benchmarks.Kernel.CheckIxeFold,
    `Benchmarks.Kernel.CheckIxeGuarded, `Benchmarks.Kernel.CheckIxeRows,
    `Benchmarks.Kernel.CheckIxeReport, `Benchmarks.Kernel.CheckIxePaired]

/-- The certified checker's environment check over a compiled `.ixe`: the
verified checker through the Ixon reader, one row per constant (untrusted
step); the records streamed (`--load eager` decodes them all up front), and
with `--jobs <n>` the checks on a pool of `n` workers. -/
lean_exe «kernel-check-ixe» where
  root := `Benchmarks.Kernel.CheckIxeMain
  moreLinkObjs := #[ix_rs]

/-- Regenerates `IxC/Kernel/Ixon/PinData.lean` (pins and prelude) from a
compiled Init (`.lake/envs/initstd.ixe`), verified by the verified fold. -/
lean_exe «kernel-pin-gen» where
  root := `Benchmarks.Kernel.PinGen
  moreLinkObjs := #[ix_rs]

/-- Run the certified kernel gate: the standalone strict build with its audits,
the host-side tests, the codec and block-order differentials against Rust,
optionally the set-theory model, the layering and trust-surface fences, the
level comparison, the certified entry's host-compiled cases, and the reader's
fidelity against Lean (the fixture closure and the first records of Init and
Std). -/
script "check-kernel" (args) := do
  unless args.isEmpty || args == ["--with-model"] do
    IO.eprintln "usage: lake run check-kernel [--with-model]"
    return 2
  let run (cmd : String) (args : Array String) : ScriptM Unit := do
    let child ← IO.Process.spawn { cmd, args, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do
      throw <| IO.userError s!"{cmd} {args} failed with exit code {code}"
  run "lake" #["-d", "IxC", "build", "--wfail"]
  run "lake" #["build", "--wfail", "Ix.Ixon.Projection.Audit", "Ix.Ixon.BlockOrder.Audit", "Tests.Ix.Kernel.BlockOrder", "Tests.Ix.Kernel.AddressPure", "Tests.Ix.Kernel.Projection", "Tests.Ix.Kernel.Reader", "Tests.Ix.Kernel.CertifiedEntry", "Tests.Ix.Kernel.ReaderRoundtrip", "Tests.Ix.Kernel.Axioms"]
  run "lake" #["build", "--wfail", "kernel-codec", "kernel-order"]
  let codec ← IO.Process.output { cmd := ".lake/build/bin/kernel-codec" }
  IO.FS.writeFile ".lake/build/kernel-codec.log" (codec.stdout ++ codec.stderr)
  IO.eprint codec.stderr
  unless codec.exitCode == 0 do
    IO.eprint codec.stdout
    throw <| IO.userError "kernel-codec failed; see .lake/build/kernel-codec.log"
  IO.println "Production Ixon codec and Rust differential checks passed."
  let order ← IO.Process.output { cmd := ".lake/build/bin/kernel-order" }
  IO.FS.writeFile ".lake/build/kernel-order.jsonl" order.stdout
  IO.eprint order.stderr
  unless order.exitCode == 0 do
    IO.eprint order.stdout
    throw <| IO.userError "kernel-order failed; see .lake/build/kernel-order.jsonl"
  if args == ["--with-model"] then
    run "lake" #["-d", "Models/SetTheory", "build", "--wfail"]
  -- The kernel's fences, derived from con-leche's: import layering and the
  -- per-file escape allowlist, with the trust-surface lexer's self-test.
  run "lake" #["build", "--wfail", "kernel-layering", "kernel-trust-surface"]
  run ".lake/build/bin/kernel-layering" #[]
  run ".lake/build/bin/kernel-trust-surface" #[]
  -- The level comparison against brute-force evaluation.
  run "lake" #["build", "--wfail", "kernel-level-comparison"]
  run ".lake/build/bin/kernel-level-comparison" #[]
  -- Host-compiled Lean declarations through the certified entry, each with
  -- an exact expected verdict (`Tests/Ix/Kernel/EntryCases.lean`).
  run "lake" #["build", "--wfail", "kernel-entry-cases"]
  let entry ← IO.Process.output { cmd := ".lake/build/bin/kernel-entry-cases" }
  IO.FS.writeFile ".lake/build/kernel-entry-cases.jsonl" entry.stdout
  IO.eprint entry.stderr
  unless entry.exitCode == 0 do
    IO.eprint entry.stdout
    throw <| IO.userError "kernel-entry-cases failed; see .lake/build/kernel-entry-cases.jsonl"
  -- The Ixon reader against a direct translation of the Lean constants it was
  -- compiled from, and the kernel's projection output against the compiler's
  -- records: the fixture closure (the `lake test` suite's check) and the
  -- first records of Init and Std (`Tests/Ix/Kernel/ReaderFidelity.lean`).
  run "lake" #["build", "--wfail", "kernel-reader-fidelity"]
  let mut fidelityLog := ""
  for mode in #["--fixture", "--check-kernel"] do
    let out ← IO.Process.output { cmd := ".lake/build/bin/kernel-reader-fidelity", args := #[mode] }
    fidelityLog := fidelityLog ++ s!"== {mode}\n{out.stdout}{out.stderr}"
    IO.FS.writeFile ".lake/build/kernel-reader-fidelity.log" fidelityLog
    IO.eprint out.stderr
    unless out.exitCode == 0 do
      IO.eprint out.stdout
      throw <| IO.userError s!"kernel-reader-fidelity {mode} failed; see .lake/build/kernel-reader-fidelity.log"
  IO.println "Reader fidelity checks passed."
  IO.println "Certified kernel checks passed."
  return 0

end IxC
