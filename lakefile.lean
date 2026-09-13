import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "ab4d5eb461941837f48eb891be755c8c73e89fdd"

/- Blake3 precompiles its libraries, so Lake loads their shared objects -- which
bundle the C and Rust FFI objects -- into any process elaborating a module that
imports them. That is what supplies the BLAKE3 backend to Lean's native evaluator
for the `native_decide` proofs in `IxKernelVerify`, so this pin must stay at or after
the revision that turned precompilation on. Before it, Blake3 exposed a
`blake3_rs_shared` cdylib that `ix_native_decide_dynlib` had to fetch and link;
that target no longer exists. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "78f5bc4b22de1172af8a5d91e7039128084fad3a"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.33.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.33.0"

/-! ## FFI

The Rust static libraries use `target` + `moreLinkObjs` instead of `extern_lib` because different Lean executables need different Cargo features:

- `ix` uses `ix_rs_net` (`parallel,net`) for networking support (iroh).
- `IxTests` uses `ix_rs_test` (`parallel,test-ffi`) for test-only FFI code.
- Everything else inherits `ix_rs` (`parallel`, plus opt-in `cuda`) from the
  `Ix` `lean_lib`.

The `ix_rs_test` and `ix_rs_net` targets fetch `ix_rs` first to guarantee ordering
before Cargo overwrites its release archive, then snapshot distinct Lake artifacts.
The second Cargo build is incremental — only feature-affected crates recompile.

`extern_lib` only runs at link time, so `lake build` on a `lean_lib` alone wouldn't trigger the Cargo build. With `target` + `moreLinkObjs`, the Rust static lib is built during module compilation on the default `Ix` lib, allowing Lake to conditional compile the Rust lib per build target.
-/
section FFI

/-- Build args for `cargo build --release` with opt-in feature overrides.
Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) (net : Bool := false) : IO (Array String) := do
  -- IX_NO_PAR=1 disables parallel; IX_CUDA=1/true/yes enables CUDA.
  let ixNoPar ← IO.getEnv "IX_NO_PAR"
  let ixCuda ← IO.getEnv "IX_CUDA"
  let mut features : Array String := #[]
  if ixNoPar != some "1" then features := features.push "parallel"
  if ixCuda == some "1" || ixCuda == some "true" || ixCuda == some "yes" then
    features := features.push "cuda"
  if net && !System.Platform.isOSX then features := features.push "net"
  if testFfi then features := features.push "test-ffi"
  IO.println s!"Ix Rust features: {if features.isEmpty then "none" else ",".intercalate features.toList}"
  let buildArgs := #["build", "--release", "-p", "ix-ffi"]
  if features.isEmpty then return buildArgs
  else return buildArgs ++ #["--features", ",".intercalate features.toList]

/-- Build and snapshot one feature selection of the Rust static library.
The copied output has a Lake trace containing both Rust sources and Cargo
arguments, so changing `IX_CUDA` cannot silently reuse a differently-featured
archive from a previous invocation. -/
def buildRustStatic (pkg : Package) (args : Array String) (tag : String) :
    SpawnM (Job FilePath) := do
  let sources ← inputDir (pkg.dir / "crates") true fun path =>
    path.extension == some "rs" || path.fileName == "Cargo.toml"
  let manifests := Job.collectArray #[
    ← inputTextFile (pkg.dir / "Cargo.toml"),
    ← inputTextFile (pkg.dir / "Cargo.lock")
  ]
  let deps := sources.zipWith (fun sourceFiles manifestFiles =>
    (sourceFiles, manifestFiles)) manifests
  let output := pkg.buildDir / "lib" / s!"libix_ffi_{tag}.a"
  buildFileAfterDep output deps (fun _ => do
    proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
    let built := pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi"
    copyFile built output
  ) (extraDepTrace := pure <| .ofHash (pureHash args) s!"cargo args: {args}")

/-- Build the Rust static lib with default features (`parallel`). -/
target ix_rs pkg : FilePath := do
  buildRustStatic pkg (← cargoArgs) "default"

/-- Rebuild the Rust static lib with `test-ffi`.
Only triggered by `lake test` (via `moreLinkObjs` on `IxTests`).
Fetches `ix_rs` first to guarantee ordering before overwriting the lib. -/
target ix_rs_test pkg : FilePath := do
  let base ← ix_rs.fetch
  base.mapM fun _ => do
    let args ← cargoArgs (testFfi := true)
    proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
    let built := pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi"
    let output := pkg.buildDir / "lib" / "libix_ffi_test.a"
    copyFile built output
    return output

/-- Build the Rust static lib with `net` for the `ix` CLI.
Fetches `ix_rs` first to guarantee ordering before overwriting the lib. -/
target ix_rs_net pkg : FilePath := do
  let base ← ix_rs.fetch
  base.mapM fun _ => do
    let args ← cargoArgs (net := true)
    proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
    let built := pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi"
    let output := pkg.buildDir / "lib" / "libix_ffi_net.a"
    copyFile built output
    return output

/-- The `ix-ffi-dyn` cdylib: Ix's own raw `@[extern]` symbols (currently the
`toLEBytes` operations) as a small standalone shared library. Consumed by
`ix_native_decide_dynlib`; kept separate from `ix-ffi` so proofs don't load
that crate's full dependency graph. -/
target ix_ffi_dyn pkg : FilePath := do
  let args := #["build", "--release", "-p", "ix-ffi-dyn"]
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToSharedLib "ix_ffi_dyn"

end FFI

@[default_target]
lean_lib Ix where
  moreLinkObjs := #[ix_rs]
  -- disabled because it breaks the binary
  --precompileModules := true

lean_exe ix where
  root := `Main
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_net]

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

end Tests

section Benchmarks

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

lean_lib IxTheoryNamed where
  roots := #[]
  globs := #[.submodules `Ix.Theory.Named]

section IxKernelVerify

/-- Loadable FFI for Lean's native evaluator while `IxKernelVerify` is elaborated.

`native_decide` runs compiled Lean before any executable is linked, so for each
opaque `@[extern]` it reaches, both symbol layers must be loadable up front:

* the boxed entry point Lean calls (`lp_..._boxed`), taken from Lean's own
  generated object for the declaring module, so no ABI is mirrored by hand; and
* the raw Rust symbol it forwards to, taken from that crate's `cdylib`, recorded
  by absolute path so no `LD_LIBRARY_PATH` is needed.

Covers Ix's own externs only -- currently `Ix.Unsigned.toLEBytes` against
`ix-ffi-dyn`. Blake3's are not here: that package precompiles its libraries, so
Lake loads their shared objects into the elaborating process by itself. -/
target ix_native_decide_dynlib pkg : Dynlib := do
  let some ixUnsigned ← findModule? `Ix.Unsigned
    | error "module `Ix.Unsigned` not found"
  -- Raw symbols come from the crate's cdylib, recorded by path, and are built
  -- by fetching the owning target (no direct cargo calls here).
  let ixCdylib ← ix_ffi_dyn.fetch
  -- Boxed entry points are Lean's own generated objects for the declaring module.
  let boxedObjs ← (ixUnsigned.nativeFacets true).mapM (·.fetch ixUnsigned)
  buildSharedLib "ix_native_decide"
    (pkg.buildDir / nameToSharedLib "ix_native_decide")
    (boxedObjs.push ixCdylib) #[]

/- Formal verification of `Ix.Kernel` against the internal named specification.
Non-default: `lake build ix` never
touches it, and `build-all` (the lint driver) skips it by name because its
internal named-specification proofs still emit named `sorry` warnings — `lake lint
-- --wfail` would otherwise fail even though the Ix verification source has
no local `sorry` tokens. Required CI builds it separately without `--wfail`,
audits the exact local sorry frontier, and checks exact per-root transitive
axiom plus direct-`sorryAx`-origin manifests. Dev loop:
`lake build IxKernelVerify`; focused trust audit:
`lake build Ix.Kernel.Verify.Audit.Completed Ix.Kernel.Verify.Audit.Conditional
Ix.Kernel.Verify.Audit.Statements`. -/
lean_lib IxKernelVerify where
  globs := #[.submodules `Ix.Kernel.Verify]
  -- `supportInterpreter` is a `lean_exe` option and takes effect only when
  -- that executable is linked, after its modules have been elaborated.
  -- These native-decide proofs need the boxed FFI symbols while the library
  -- modules are being elaborated, so they must be supplied as a dynlib.
  dynlibs := #[ix_native_decide_dynlib]

end IxKernelVerify

/- Refinement of production kernel operations into the new consistency model.
Checked independently so its proved roots have their own axiom boundary. -/
lean_lib IxKernelConsistency where
  roots := #[`Ix.Kernel.Verify.Consistency]
  globs := #[.andSubmodules `Ix.Kernel.Verify.Consistency]

/- Compiler and verifier-binding components with an independent exact audit. -/
lean_lib IxAiurVerify where
  roots := #[`Ix.Aiur.Proofs]
  globs := #[.andSubmodules `Ix.Aiur.Proofs]

lean_exe «aiur-backend-tests» where
  root := `Tests.Aiur.Backend

lean_exe «aiur-bytecode-tests» where
  root := `Tests.Aiur.BytecodeCompare
  supportInterpreter := true

lean_exe «aiur-dedup-tests» where
  root := `Tests.Aiur.Dedup
  supportInterpreter := true

lean_exe «aiur-tail-match-tests» where
  root := `Tests.Aiur.TailMatches
  supportInterpreter := true

lean_exe «aiur-source-value-tests» where
  root := `Tests.Aiur.SourceValues
  supportInterpreter := true

lean_exe «aiur-hoisting-tests» where
  root := `Tests.Aiur.Hoisting
  supportInterpreter := true

lean_exe «aiur-air-tests» where
  root := `Tests.Aiur.AIRSemantics

lean_exe «aiur-byte-gadget-tests» where
  root := `Tests.Aiur.ByteGadgets

lean_exe «aiur-lookup-shape-tests» where
  root := `Tests.Aiur.LookupShapes

lean_exe «aiur-lookup-budget-tests» where
  root := `Tests.Aiur.LookupBudget

lean_exe «aiur-selector-control-tests» where
  root := `Tests.Aiur.SelectorControl

lean_exe «aiur-operation-row-tests» where
  root := `Tests.Aiur.OperationRows

lean_exe «aiur-block-row-tests» where
  root := `Tests.Aiur.BlockRows

lean_exe «aiur-circuit-row-tests» where
  root := `Tests.Aiur.CircuitRows

lean_exe «aiur-memory-row-tests» where
  root := `Tests.Aiur.MemoryRows

lean_exe «aiur-trace-height-tests» where
  root := `Tests.Aiur.TraceHeights

lean_exe «aiur-expression-graph-tests» where
  root := `Tests.Aiur.ExpressionGraph

lean_exe «aiur-constant-degree-tests» where
  root := `Tests.Aiur.ConstantDegree

lean_exe «aiur-frontend-expression-tests» where
  root := `Tests.Aiur.FrontendExpressions

lean_exe «aiur-graph-compilation-tests» where
  root := `Tests.Aiur.GraphCompilation

lean_exe «aiur-operation-expression-tests» where
  root := `Tests.Aiur.OperationExpressions

section IxCompileVerify

/- Formal verification of the Lean-to-Ixon compiler against the same
internal named-specification endpoint as `IxKernelVerify`.  Kept as a separate non-default
library so compiler proofs cannot accidentally inherit checker acceptance
theorems as their specification. -/
lean_lib IxCompileVerify where
  globs := #[.submodules `Ix.Compile.Verify]

end IxCompileVerify

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

  -- Copy the ix binary into the target directory
  let tgtPath := binDir / "ix"
  let srcBytes ← FS.readBinFile $ ".lake" / "build" / "bin" / "ix"
  FS.writeBinFile tgtPath srcBytes

  -- Set access rights for the newly created file
  let fullAccess := { read := true, write := true, execution := true }
  let noWriteAccess := { fullAccess with write := false }
  let fileRight := { user := fullAccess, group := fullAccess, other := noWriteAccess }
  setAccessRights tgtPath fileRight
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
  let libNames := pkg.configTargets LeanLib.configKind |>.map (·.name.toString false)
  let exeNames := pkg.configTargets LeanExe.configKind |>.map (·.name.toString false)
  -- IxKernelVerify is the WIP proofs lib: sorry-bearing by design while the
  -- verification frontier is open, so it must not run under `--wfail`.
  -- Required CI builds it separately and audits the exact frontier.
  -- Compiler and theory checks have dedicated CI jobs and scripts below.
  let allNames := (libNames ++ exeNames |>.toList).filter fun name =>
    name != "IxKernelVerify" && name != "IxCompileVerify" && !name.startsWith "IxCompiler" &&
      !name.startsWith "IxTheory" && !name.startsWith "compiler-" &&
      !name.startsWith "theory-"
  for name in allNames do
    IO.println s!"Building: {name}"
    let child ← IO.Process.spawn {
      cmd := "lake", args := #["build", name] ++ args
      stdout := .inherit, stderr := .inherit }
    let exitCode ← child.wait
    if exitCode != 0 then return exitCode
  return 0

end Scripts

section Compiler

/- Independent compiler and theory imports. These are not dependencies of
the production Ix umbrella or CLI. Their checks run in separate CI jobs. -/
target compiler_hpt_cache_sync pkg : FilePath := do
  let source ← inputTextFile <| pkg.dir / "native/compiler/hpt_cache_sync.c"
  let object := pkg.buildDir / "native" / "compiler_hpt_cache_sync.o"
  let includeDir ← getLeanIncludeDir
  buildO object source #["-fPIC", "-I", includeDir.toString] #[] "cc" getLeanTrace

lean_lib IxCompiler where
  roots := #[`Ix.Compiler]
  globs := #[.andSubmodules `Ix.Compiler]
  moreLinkObjs := #[compiler_hpt_cache_sync]

lean_lib IxCompilerTests where
  roots := #[`Tests.Compiler]
  globs := #[]

lean_lib IxCompilerBench where
  roots := #[`Benchmarks.Compiler]

lean_exe «compiler-benchmark» where
  root := `Benchmarks.Compiler

lean_exe «compiler-tests» where
  root := `Tests.Compiler.Tests

lean_exe «compiler-catalog-contact» where
  root := `Tests.Compiler.CatalogContact

lean_exe «compiler-x86-object-fixture» where
  root := `Tests.Compiler.X86ObjectFixture

lean_exe «compiler-source-coverage» where
  root := `Tests.Compiler.SourceCoverage

lean_exe «compiler-source-recursion» where
  root := `Tests.Compiler.SourceRecursion

lean_exe «compiler-source-call-reuse» where
  root := `Tests.Compiler.SourceCallReuse

lean_exe «compiler-source-unique-reuse» where
  root := `Tests.Compiler.SourceUniqueReuse

lean_exe «compiler-source-native-unique» where
  root := `Tests.Compiler.SourceNativeUnique

lean_exe «compiler-source-native-runtime» where
  root := `Tests.Compiler.SourceNativeRuntime

lean_exe «compiler-source-native-upstream» where
  root := `Tests.Compiler.SourceNativeUpstream

lean_exe «compiler-source-native-scalar» where
  root := `Tests.Compiler.SourceNativeScalar

lean_exe «compiler-source-native-physical-scalar» where
  root := `Tests.Compiler.SourceNativePhysicalScalar

lean_exe «compiler-source-native-captured-scalar» where
  root := `Tests.Compiler.SourceNativeCapturedScalar

lean_exe «compiler-source-borrow» where
  root := `Tests.Compiler.SourceBorrow

lean_exe «compiler-source-borrow-runtime» where
  root := `Tests.Compiler.SourceBorrowRuntime

lean_exe «compiler-check-x86-encoder» where
  root := `Tests.Compiler.Checks.CheckX86Encoder

lean_exe «compiler-check-x86-bytes» where
  root := `Tests.Compiler.Checks.CheckX86Bytes

lean_exe «compiler-check-x86-streams» where
  root := `Tests.Compiler.Checks.CheckX86Streams

lean_exe «compiler-check-x86-object» where
  root := `Tests.Compiler.Checks.CheckX86Object

lean_exe «compiler-check-trusted-externs» where
  root := `Tests.Compiler.Checks.CheckTrustedExterns

lean_exe «compiler-check-source-coverage» where
  root := `Tests.Compiler.Checks.CheckSourceCoverage

lean_exe «compiler-check-source-recursion» where
  root := `Tests.Compiler.Checks.CheckSourceRecursion

lean_exe «compiler-check-source-call-reuse» where
  root := `Tests.Compiler.Checks.CheckSourceCallReuse

lean_exe «compiler-check-source-unique-reuse» where
  root := `Tests.Compiler.Checks.CheckSourceUniqueReuse

lean_exe «compiler-check-source-native-unique» where
  root := `Tests.Compiler.Checks.CheckSourceNativeUnique

lean_exe «compiler-check-source-native-runtime» where
  root := `Tests.Compiler.Checks.CheckSourceNativeRuntime

lean_exe «compiler-check-source-native-upstream» where
  root := `Tests.Compiler.Checks.CheckSourceNativeUpstream

lean_exe «compiler-check-source-native-scalar» where
  root := `Tests.Compiler.Checks.CheckSourceNativeScalar

lean_exe «compiler-check-source-native-physical-scalar» where
  root := `Tests.Compiler.Checks.CheckSourceNativePhysicalScalar

lean_exe «compiler-check-source-native-captured-scalar» where
  root := `Tests.Compiler.Checks.CheckSourceNativeCapturedScalar

lean_exe «compiler-check-source-borrow» where
  root := `Tests.Compiler.Checks.CheckSourceBorrow

lean_exe «compiler-check-source-borrow-runtime» where
  root := `Tests.Compiler.Checks.CheckSourceBorrowRuntime

lean_exe «compiler-check-tools-tests» where
  root := `Tests.Compiler.Checks.CheckToolsTests

end Compiler

section Theory

lean_lib IxTheory where
  roots := #[`Ix.Theory]
  -- The set model has its own import graph and trust audit. Named kernel
  -- proof support belongs to IxTheoryNamed and is checked separately.
  globs := #[.one `Ix.Theory, .one `Ix.Theory.Certified,
    .one `Ix.Theory.Const, .one `Ix.Theory.Expr, .one `Ix.Theory.Quot,
    .one `Ix.Theory.Ref, .one `Ix.Theory.Rename, .one `Ix.Theory.Store,
    .one `Ix.Theory.VLevel, .submodules `Ix.Theory.Certificate,
    .submodules `Ix.Theory.Certified, .submodules `Ix.Theory.Inductive,
    .submodules `Ix.Theory.Model, .submodules `Ix.Theory.Std]

lean_lib IxTheoryCertified where
  roots := #[`Ix.Theory.Certified]

lean_lib IxTheoryTests where
  roots := #[`Tests.Theory]

lean_exe «theory-provenance» where
  root := `Tests.Theory.Provenance

end Theory

section Certified

lean_lib IxCertified where
  roots := #[`Ix.Certified]
  moreLinkObjs := #[ix_rs]

lean_lib IxCertifiedAudit where
  roots := #[`Ix.Certified.AuditAll]

lean_exe "certified-cli-tests" where
  root := `Tests.Certified.CLI
  supportInterpreter := true

lean_exe "certified-adapter-tests" where
  root := `Tests.Certified.Check
  supportInterpreter := true

lean_exe «certified-check» where
  root := `Ix.Certified.Main
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-claim-check» where
  root := `Ix.Certified.ClaimMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-feature-tests» where
  root := `Tests.Certified.Features
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-ordinary-tests» where
  root := `Tests.Certified.Ordinary
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-vm-tests» where
  root := `Tests.Certified.VM
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-source-tests» where
  root := `Tests.Certified.SourceMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-fidelity-tests» where
  root := `Tests.Certified.FidelityMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-claim-tests» where
  root := `Tests.Certified.ClaimsMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-modeled-tests» where
  root := `Tests.Certified.ModeledMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

end Certified

namespace ComponentChecks

private def run (command : String) (args : Array String := #[]) : IO Unit := do
  IO.println s!"Running: {command} {String.intercalate " " args.toList}"
  let child ← IO.Process.spawn { cmd := command, args, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do throw (IO.userError s!"{command} failed ({code})")

private def compilerExe (name : String) : String := s!".lake/build/bin/compiler-{name}"

end ComponentChecks

open ComponentChecks

/-- Build every compiler target, then exercise independent byte/native checks. -/
script "check-compiler" := do
  let pkg ← getRootPackage
  let executables := pkg.configTargets LeanExe.configKind |>.map (·.name.toString false)
    |>.filter (·.startsWith "compiler-")
  run "lake" (#["build", "IxCompiler"] ++ executables)
  for name in ["tests", "check-trusted-externs", "check-tools-tests",
      "check-x86-encoder", "check-x86-bytes", "check-x86-streams"] do
    run (compilerExe name)
  let host ← IO.Process.output { cmd := "uname", args := #["-sm"] }
  unless host.exitCode == 0 do throw (IO.userError "unable to identify native test host")
  let native := host.stdout.trimAscii.toString == "Linux x86_64"
  let nativeArgs (fixture : String) : Array String := if native then
    #["--cc", "cc", "--harness", s!"Tests/Fixtures/Compiler/{fixture}/native_harness.c"] else #[]
  run (compilerExe "check-x86-object")
    (#["--fixture", compilerExe "x86-object-fixture"] ++ nativeArgs "x86")
  run (compilerExe "check-source-coverage")
    (#["--fixture", compilerExe "source-coverage"] ++ nativeArgs "x86")
  for name in ["source-recursion", "source-call-reuse", "source-unique-reuse",
      "source-borrow", "source-borrow-runtime"] do
    run (compilerExe s!"check-{name}") #["--fixture", compilerExe name]
  for name in ["source-native-unique", "source-native-runtime", "source-native-upstream",
      "source-native-scalar", "source-native-physical-scalar", "source-native-captured-scalar"] do
    run (compilerExe s!"check-{name}") (#["--fixture", compilerExe name] ++ nativeArgs name)
  run (compilerExe "check-source-native-runtime")
    (#["--fixture", compilerExe "source-native-runtime", "--variant", "counter-fold"] ++
      nativeArgs "source-native-runtime")
  run (compilerExe "benchmark") #["analysis-self-check"]
  IO.println s!"Compiler checks passed (native execution: {native})."
  return 0

/-- Check the selected theory, its provenance, and the exact foundation report. -/
script "check-theory" := do
  run "lake" #["build", "--wfail", "IxTheory", "IxTheoryTests", "theory-provenance"]
  run ".lake/build/bin/theory-provenance"
  let report ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "Tests/Theory/Audit/Certified.lean"] }
  unless report.exitCode == 0 do throw (IO.userError s!"{report.stdout}{report.stderr}")
  let expected ← IO.FS.readFile "Tests/Theory/certified-foundation.txt"
  unless report.stdout == expected do
    IO.FS.withTempFile fun handle path => do
      handle.putStr report.stdout
      handle.flush
      let child ← IO.Process.spawn {
        cmd := "diff", args := #["-u", "Tests/Theory/certified-foundation.txt", path.toString]
        stdout := .inherit, stderr := .inherit }
      let _ ← child.wait
      throw (IO.userError "certified foundation report differs from the reviewed manifest")
  IO.println "Theory checks passed: exact root types, axioms, dependencies, and runtime inventory."
  return 0

/-- Audit Aiur components and exercise their actual native verifier binding. -/
script "check-aiur" := do
  run "lake" #["build", "--wfail", "IxAiurVerify", "aiur-backend-tests",
    "aiur-bytecode-tests", "aiur-dedup-tests", "aiur-tail-match-tests", "aiur-source-value-tests",
    "aiur-hoisting-tests", "aiur-air-tests", "aiur-byte-gadget-tests", "aiur-lookup-shape-tests",
    "aiur-lookup-budget-tests", "aiur-selector-control-tests", "aiur-operation-row-tests",
    "aiur-block-row-tests", "aiur-circuit-row-tests", "aiur-memory-row-tests", "aiur-trace-height-tests",
    "aiur-expression-graph-tests", "aiur-constant-degree-tests", "aiur-frontend-expression-tests",
    "aiur-graph-compilation-tests", "aiur-operation-expression-tests"]
  let report ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "-DwarningAsError=true", "Ix/Aiur/Proofs/Audit.lean"] }
  unless report.exitCode == 0 do throw (IO.userError s!"{report.stdout}{report.stderr}")
  let expectedPath := "Tests/Aiur/backend-foundation.txt"
  let expected ← IO.FS.readFile expectedPath
  unless report.stdout == expected do
    IO.FS.withTempFile fun handle path => do
      handle.putStr report.stdout
      handle.flush
      let child ← IO.Process.spawn {
        cmd := "diff", args := #["-u", expectedPath, path.toString]
        stdout := .inherit, stderr := .inherit }
      let _ ← child.wait
      throw (IO.userError "Aiur component report differs from the reviewed manifest")
  let snapshots : Array (String × Array String × String) := #[
    ("aiur-bytecode-tests", #[], "Tests/Aiur/bytecode-compatibility.txt"),
    ("aiur-dedup-tests", #["--snapshot"], "Tests/Aiur/dedup-compatibility.txt"),
    ("aiur-tail-match-tests", #[], "Tests/Aiur/tail-match-compatibility.txt"),
    ("aiur-source-value-tests", #[], "Tests/Aiur/source-value-compatibility.txt")]
  for (program, args, comparisonPath) in snapshots do
    let comparison ← IO.Process.output { cmd := s!".lake/build/bin/{program}", args }
    unless comparison.exitCode == 0 && comparison.stderr.isEmpty do
      throw (IO.userError s!"{comparison.stdout}{comparison.stderr}")
    unless comparison.stdout == (← IO.FS.readFile comparisonPath) do
      IO.FS.withTempFile fun handle path => do
        handle.putStr comparison.stdout
        handle.flush
        let child ← IO.Process.spawn {
          cmd := "diff", args := #["-u", comparisonPath, path.toString]
          stdout := .inherit, stderr := .inherit }
        let _ ← child.wait
        throw (IO.userError s!"{program} differs from its original native snapshot")
  run ".lake/build/bin/aiur-dedup-tests"
  run ".lake/build/bin/aiur-hoisting-tests"
  run ".lake/build/bin/aiur-air-tests"
  run ".lake/build/bin/aiur-constant-degree-tests"
  IO.FS.withTempDir fun directory => do
    let snapshot := directory / "native-byte-gadgets.bin"
    let shapeSnapshot := directory / "native-lookup-shapes.bin"
    let budgetSnapshot := directory / "native-lookup-budget.bin"
    let selectorSnapshot := directory / "native-selector-control.bin"
    let operationSnapshot := directory / "native-operation-rows.bin"
    let blockSnapshot := directory / "native-block-rows.bin"
    let circuitSnapshot := directory / "native-circuit-rows.bin"
    let memorySnapshot := directory / "native-memory-rows.bin"
    let traceHeightSnapshot := directory / "native-trace-heights.bin"
    let graphShapeSnapshot := directory / "native-graph-shapes.bin"
    let expressionGraphSnapshot := directory / "native-expression-graphs.bin"
    let constantDegreeSnapshot := directory / "native-constant-degree-rows.bin"
    let frontendSnapshot := directory / "native-frontend-expressions.bin"
    let compilationSnapshot := directory / "native-graph-compilation.bin"
    let operationExpressionSnapshot := directory / "native-operation-expressions.bin"
    let exporter ← IO.Process.spawn {
      cmd := "cargo"
      args := #["test", "--locked", "--release", "-p", "aiur",
        "_snapshot"]
      env := #[("IX_BYTE_GADGET_SNAPSHOT", some snapshot.toString),
        ("IX_LOOKUP_SHAPE_SNAPSHOT", some shapeSnapshot.toString),
        ("IX_LOOKUP_BUDGET_SNAPSHOT", some budgetSnapshot.toString),
        ("IX_SELECTOR_CONTROL_SNAPSHOT", some selectorSnapshot.toString),
        ("IX_OPERATION_ROW_SNAPSHOT", some operationSnapshot.toString),
        ("IX_BLOCK_ROW_SNAPSHOT", some blockSnapshot.toString),
        ("IX_CIRCUIT_ROW_SNAPSHOT", some circuitSnapshot.toString),
        ("IX_MEMORY_ROW_SNAPSHOT", some memorySnapshot.toString),
        ("IX_FIXED_TRACE_HEIGHT_SNAPSHOT", some traceHeightSnapshot.toString),
        ("IX_GRAPH_SHAPE_SNAPSHOT", some graphShapeSnapshot.toString),
        ("IX_EXPRESSION_GRAPH_SNAPSHOT", some expressionGraphSnapshot.toString),
        ("IX_CONSTANT_DEGREE_ROW_SNAPSHOT", some constantDegreeSnapshot.toString),
        ("IX_FRONTEND_EXPRESSION_SNAPSHOT", some frontendSnapshot.toString),
        ("IX_GRAPH_COMPILATION_SNAPSHOT", some compilationSnapshot.toString),
        ("IX_OPERATION_EXPRESSION_SNAPSHOT", some operationExpressionSnapshot.toString)]
      stdout := .inherit
      stderr := .inherit }
    unless (← exporter.wait) == 0 do
      throw (IO.userError "native Aiur component snapshot export failed")
    run ".lake/build/bin/aiur-byte-gadget-tests" #[snapshot.toString]
    run ".lake/build/bin/aiur-lookup-shape-tests" #[shapeSnapshot.toString]
    run ".lake/build/bin/aiur-lookup-budget-tests" #[budgetSnapshot.toString]
    run ".lake/build/bin/aiur-selector-control-tests" #[selectorSnapshot.toString]
    run ".lake/build/bin/aiur-operation-row-tests" #[operationSnapshot.toString, constantDegreeSnapshot.toString]
    run ".lake/build/bin/aiur-frontend-expression-tests" #[frontendSnapshot.toString]
    run ".lake/build/bin/aiur-graph-compilation-tests" #[compilationSnapshot.toString]
    run ".lake/build/bin/aiur-operation-expression-tests" #[operationExpressionSnapshot.toString]
    run ".lake/build/bin/aiur-block-row-tests" #[blockSnapshot.toString]
    run ".lake/build/bin/aiur-circuit-row-tests" #[circuitSnapshot.toString]
    run ".lake/build/bin/aiur-memory-row-tests" #[memorySnapshot.toString]
    run ".lake/build/bin/aiur-trace-height-tests" #[traceHeightSnapshot.toString]
    run ".lake/build/bin/aiur-expression-graph-tests" #[graphShapeSnapshot.toString, expressionGraphSnapshot.toString]
  run ".lake/build/bin/aiur-backend-tests"
  IO.println "Aiur component checks passed: exact proof/runtime boundaries, compiler compatibility and native binding."
  return 0

/-- Validate certified host adapters against exact audits and frozen C7 evidence. -/
script "check-certified" := do
  run "lake" #["build", "--wfail", "IxCertified", "IxCertifiedAudit",
    "certified-check", "certified-claim-check", "certified-feature-tests",
    "certified-ordinary-tests", "certified-vm-tests", "certified-source-tests",
    "certified-fidelity-tests", "certified-claim-tests", "certified-modeled-tests",
    "certified-cli-tests", "certified-adapter-tests"]
  let report ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "-DwarningAsError=true", "Ix/Certified/AuditAll.lean"] }
  unless report.exitCode == 0 do throw (IO.userError s!"{report.stdout}{report.stderr}")
  let expectedPath := "Tests/Certified/foundation.txt"
  unless report.stdout == (← IO.FS.readFile expectedPath) do
    IO.FS.withTempFile fun handle path => do
      handle.putStr report.stdout
      handle.flush
      let child ← IO.Process.spawn {
        cmd := "diff", args := #["-u", expectedPath, path.toString]
        stdout := .inherit, stderr := .inherit }
      let _ ← child.wait
      throw (IO.userError "certified adapter report differs from the reviewed manifest")
  run ".lake/build/bin/certified-adapter-tests"
  return 0
