import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "ab4d5eb461941837f48eb891be755c8c73e89fdd"

/- Blake3's `blake3_rs_shared` target builds `blake3-rs` as a `cdylib`
alongside the staticlib. `ix_native_decide_dynlib` fetches it to supply the
BLAKE3 backend to Lean's native evaluator, and that dynlib gates every
`IxTcVerify` module, so this pin must stay at or after the revision that
introduced the target. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "e6e908bfd3af607ab44fb462fa2276a2c81addba"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.33.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.33.0"

/- Reference Lean4-in-Lean4 theory and checker. `IxTcVerify` imports its
Theory/Verify specification surface, while `bench-lean4lean` and the ignored
`lean4lean` test runner exercise the implementation. The default `ix` target
still does not build this dependency. Pin `argumentcomputer/lean4ix` exactly --
the Argument development line, a standalone repository rather than a GitHub
fork of digama0/lean4lean: this revision carries the upstream v4.32/v4.33
kernel hardening — including the `checkNoMVarNoFVar` check on an opaque's
value (leanprover/lean4#14498), which the replay path in
`Benchmarks/Lean4Lean.lean` reaches — on top of that line's certified
inductive-environment and projection development, and tracks Lean v4.33.1 as
this package does. -/
require lean4lean from git
  "https://github.com/argumentcomputer/lean4ix" @ "a4188d7c2979378d85c6bb41fdd96c3a48a71371"

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

/- The lean4lean replay machinery as an importable lib: the
`bench-lean4lean` exe root and the ignored `lean4lean` test runner both
import `Benchmarks.Lean4Lean`, and modules under `Benchmarks/` belong to
no other lib target, so without this Lake cannot schedule the module from
the Tests import graph. -/
lean_lib Lean4LeanBench where
  globs := #[.one `Benchmarks.Lean4Lean]

lean_exe «bench-lean4lean» where
  root := `Benchmarks.Lean4LeanMain
  supportInterpreter := true

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

section IxTcVerify

/-- Loadable FFI for Lean's native evaluator while `IxTcVerify` is elaborated.

`native_decide` runs compiled Lean before any executable is linked, so for each
opaque `@[extern]` it reaches, both symbol layers must be loadable up front:

* the boxed entry point Lean calls (`lp_..._boxed`), taken from Lean's own
  generated object for the declaring module, so no ABI is mirrored by hand; and
* the raw Rust symbol it forwards to, taken from that crate's `cdylib`, recorded
  by absolute path so no `LD_LIBRARY_PATH` is needed.

Covered externs: `Blake3.Rust` hashing (with the `Blake3` base module, which
holds the `HasherOps.hash` orchestration `Address.blake3` calls) against
`blake3_rs`, and `Ix.Unsigned.toLEBytes` against `ix-ffi-dyn`. -/
target ix_native_decide_dynlib pkg : Dynlib := do
  let some blake3Base ← findModule? `Blake3
    | error "module `Blake3` not found; is the Blake3 dependency available?"
  let some blake3Rust ← findModule? `Blake3.Rust
    | error "module `Blake3.Rust` not found; is the Blake3 dependency available?"
  let some ixUnsigned ← findModule? `Ix.Unsigned
    | error "module `Ix.Unsigned` not found"
  -- Raw symbols come from each crate's cdylib, recorded by path, and are built
  -- by fetching the owning package's target (no direct cargo calls here):
  -- Blake3 via its `blake3_rs_shared`, Ix via the minimal `ix_ffi_dyn`.
  let blake3Cdylib := (← blake3Rust.pkg.fetchTargetJob `blake3_rs_shared).map fun _ =>
    blake3Rust.pkg.dir / "rust" / "target" / "release" / nameToSharedLib "blake3_rs"
  let ixCdylib ← ix_ffi_dyn.fetch
  -- Boxed entry points are Lean's own generated objects for the declaring modules.
  let mut boxedObjs := #[]
  for mod in #[blake3Base, blake3Rust, ixUnsigned] do
    boxedObjs := boxedObjs ++ (← (mod.nativeFacets true).mapM (·.fetch mod))
  buildSharedLib "ix_native_decide"
    (pkg.buildDir / nameToSharedLib "ix_native_decide")
    (boxedObjs.push blake3Cdylib |>.push ixCdylib) #[]

/- Formal verification of `Ix.Tc` against the lean4lean `Theory` spec.
Non-default: `lake build ix` never
touches it, and `build-all` (the lint driver) skips it by name because its
pinned Lean4Lean dependencies still emit named `sorry` warnings — `lake lint
-- --wfail` would otherwise fail even though the Ix verification source has
no local `sorry` tokens. Required CI builds it separately without `--wfail`,
audits the exact local sorry frontier, and checks exact per-root transitive
axiom plus direct-`sorryAx`-origin manifests. Dev loop:
`lake build IxTcVerify`; focused trust audit:
`lake build Ix.Tc.Verify.Audit.Completed Ix.Tc.Verify.Audit.Statements`. -/
lean_lib IxTcVerify where
  globs := #[.submodules `Ix.Tc.Verify]
  -- `supportInterpreter` is a `lean_exe` option and takes effect only when
  -- that executable is linked, after its modules have been elaborated.
  -- These native-decide proofs need the boxed FFI symbols while the library
  -- modules are being elaborated, so they must be supplied as a dynlib.
  dynlibs := #[ix_native_decide_dynlib]

end IxTcVerify

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
  -- IxTcVerify is the WIP proofs lib: sorry-bearing by design while the
  -- verification frontier is open, so it must not run under `--wfail`.
  -- Required CI builds it separately and audits the exact frontier.
  let allNames := (libNames ++ exeNames |>.toList).filter (· != "IxTcVerify")
  for name in allNames do
    IO.println s!"Building: {name}"
    let child ← IO.Process.spawn {
      cmd := "lake", args := #["build", name] ++ args
      stdout := .inherit, stderr := .inherit }
    let exitCode ← child.wait
    if exitCode != 0 then return exitCode
  return 0

end Scripts
