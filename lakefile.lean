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

/- Legacy formal verification of `Ix.Kernel` against the internal named
specification (`Ix.Theory.Named`, Lean4Lean-derived). This track is being
retired in favour of the set model (`Ix.Theory.Model`); the required kernel
proof gate is `IxKernelConsistency` below, whose audit rejects any
`Ix.Theory.Named` module in its import closure. Non-default: `lake build ix`
never touches it, and `build-all` (the lint driver) skips it by name because
its named-specification proofs still emit named `sorry` warnings — `lake lint
-- --wfail` would otherwise fail even though the Ix verification source has
no local `sorry` tokens. It is not part of required CI: the non-required
`named-spec-verification` workflow (manual or weekly) builds it without
`--wfail`, audits the exact local sorry frontier, and checks exact per-root
transitive axiom plus direct-`sorryAx`-origin manifests. Dev loop:
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

/- Direct production refinement, including the atomic environment fragment,
with its own exact axiom audit. Whole-checker soundness remains separate. -/
lean_lib IxKernelConsistency where
  roots := #[`Ix.Kernel.Verify.Consistency]
  globs := #[.andSubmodules `Ix.Kernel.Verify.Consistency]

section IxCompileVerify

/- Formal verification of the Lean-to-Ixon compiler. It still targets the
legacy named-specification syntax (`Ix.Theory.Named.VExpr`) that
`IxKernelVerify` uses, so it transitively builds part of that non-required
track until the compiler relation is retargeted to the set model. Required CI
builds it on its own (`lake build IxCompileVerify`). Kept as a separate
non-default library so compiler proofs cannot accidentally inherit checker
acceptance theorems as their specification. -/
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
  let libNames := pkg.configTargets LeanLib.configKind |>.map (·.name.toString)
  let exeNames := pkg.configTargets LeanExe.configKind |>.map (·.name.toString)
  -- The legacy named specification and the implementation proofs stated
  -- against it retain an audited frontier; the non-required
  -- named-spec-verification workflow builds them without `--wfail`, and
  -- required CI builds `IxCompileVerify` on its own. The set model, direct
  -- consistency roots, and certified adapters are checked strictly.
  let allNames := (libNames ++ exeNames |>.toList).filter fun name =>
    name != "IxKernelVerify" && name != "IxCompileVerify" && name != "IxTheoryNamed"
  for name in allNames do
    IO.println s!"Building: {name}"
    let child ← IO.Process.spawn {
      cmd := "lake", args := #["build", name] ++ args
      stdout := .inherit, stderr := .inherit }
    let exitCode ← child.wait
    if exitCode != 0 then return exitCode
  return 0

end Scripts

section Theory

lean_lib IxTheory where
  roots := #[`Ix.Theory]
  -- Keep the set-model foundation independent of named checker proof support.
  globs := #[.one `Ix.Theory, .one `Ix.Theory.Certified,
    .one `Ix.Theory.Const, .one `Ix.Theory.Expr, .one `Ix.Theory.Quot,
    .one `Ix.Theory.Ref, .one `Ix.Theory.Rename, .one `Ix.Theory.Store,
    .one `Ix.Theory.VLevel, .one `Ix.Theory.VLevelLemmas, .submodules `Ix.Theory.Certificate,
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

lean_exe «certified-cli-tests» where
  root := `Tests.Certified.CLI
  supportInterpreter := true

lean_exe «certified-input-tests» where
  root := `Tests.Certified.Inputs
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «certified-adapter-tests» where
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

namespace KernelChecks

private def run (command : String) (args : Array String := #[]) : IO Unit := do
  let child ← IO.Process.spawn { cmd := command, args, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do throw (IO.userError s!"{command} failed ({code})")

private def checkReport (module expectedPath : String) : IO Unit := do
  let report ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "-DwarningAsError=true", module] }
  unless report.exitCode == 0 do throw (IO.userError s!"{report.stdout}{report.stderr}")
  unless report.stdout == (← IO.FS.readFile expectedPath) do
    IO.FS.withTempFile fun handle path => do
      handle.putStr report.stdout
      handle.flush
      let child ← IO.Process.spawn {
        cmd := "diff", args := #["-u", expectedPath, path.toString]
        stdout := .inherit, stderr := .inherit }
      let _ ← child.wait
      throw (IO.userError s!"foundation report differs from {expectedPath}")

end KernelChecks

open KernelChecks

/-- Check the set model, its provenance, and its exact foundation report. -/
script "check-theory" := do
  run "lake" #["build", "--wfail", "IxTheory", "IxTheoryTests", "theory-provenance"]
  run ".lake/build/bin/theory-provenance"
  checkReport "Tests/Theory/Audit/Certified.lean" "Tests/Theory/certified-foundation.txt"
  IO.println "Theory checks passed: exact root types, axioms, dependencies, and runtime inventory."
  return 0

/-- Check host certification against exact audits and frozen source/claim evidence. -/
script "check-certified" := do
  run "lake" #["build", "--wfail", "IxCertified", "IxCertifiedAudit",
    "certified-check", "certified-claim-check", "certified-feature-tests",
    "certified-ordinary-tests", "certified-source-tests", "certified-fidelity-tests",
    "certified-claim-tests", "certified-modeled-tests", "certified-cli-tests", "certified-input-tests",
    "certified-adapter-tests"]
  checkReport "Ix/Certified/AuditAll.lean" "Tests/Certified/foundation.txt"
  run ".lake/build/bin/certified-adapter-tests"
  return 0

/-- Run the kernel implementation, consistency, foundation, and host checks. -/
script "check-kernel" (args) := do
  unless args.isEmpty || args == ["--with-model"] do
    IO.eprintln "usage: lake run check-kernel [--with-model]"
    return 2
  run "lake" #["build", "IxKernelVerify", "IxCompileVerify"]
  run "lake" #["build", "--wfail", "IxKernelConsistency"]
  run "lake" #["run", "check-theory"]
  run "lake" #["run", "check-certified"]
  run "lake" #["test", "--wfail", "--", "tc-unit"]
  if args == ["--with-model"] then
    run "lake" #["-d", "Models/SetTheory", "build", "--wfail"]
  IO.println "Kernel certification checks passed."
  return 0
