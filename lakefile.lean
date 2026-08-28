import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "ab4d5eb461941837f48eb891be755c8c73e89fdd"

/- Blake3 precompiles its libraries, so Lake loads their shared objects -- which
bundle the C and Rust FFI objects -- into any process elaborating a module that
imports them. That is what supplies the BLAKE3 backend to Lean's native evaluator
for the `native_decide` proofs in `IxTcVerify`, so this pin must stay at or after
the revision that turned precompilation on. Before it, Blake3 exposed a
`blake3_rs_shared` cdylib that `ix_native_decide_dynlib` had to fetch and link;
that target no longer exists. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "5ff5e70b6c7fc371cc6b454b83844f1f5b44ac96"

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
- Everything else inherits `ix_rs` (`parallel` only) from the `Ix` `lean_lib`.

The `ix_rs_test` and `ix_rs_net` targets fetch `ix_rs` first to guarantee ordering
before overwriting the lib, since they write to the same lib path. The second cargo build is incremental — only the feature-affected crates recompile.

`extern_lib` only runs at link time, so `lake build` on a `lean_lib` alone wouldn't trigger the Cargo build. With `target` + `moreLinkObjs`, the Rust static lib is built during module compilation on the default `Ix` lib, allowing Lake to conditional compile the Rust lib per build target.
-/
section FFI

/-- Build args for `cargo build --release` with feature flags from env vars.
Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) (net : Bool := false) : IO (Array String) := do
  -- IX_NO_PAR=1 disables parallel
  let ixNoPar ← IO.getEnv "IX_NO_PAR"
  let mut features : Array String := #[]
  if ixNoPar != some "1" then features := features.push "parallel"
  if net && !System.Platform.isOSX then features := features.push "net"
  if testFfi then features := features.push "test-ffi"
  let buildArgs := #["build", "--release", "-p", "ix-ffi"]
  if features.isEmpty then return buildArgs
  else return buildArgs ++ #["--features", ",".intercalate features.toList]

/-- Build the Rust static lib with default features (`parallel`). -/
target ix_rs pkg : FilePath := do
  let args ← cargoArgs
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi"

/-- Rebuild the Rust static lib with `test-ffi`.
Only triggered by `lake test` (via `moreLinkObjs` on `IxTests`).
Fetches `ix_rs` first to guarantee ordering before overwriting the lib. -/
target ix_rs_test pkg : FilePath := do
  let _ ← ix_rs.fetch
  let args ← cargoArgs (testFfi := true)
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi"

/-- Build the Rust static lib with `net` for the `ix` CLI.
Fetches `ix_rs` first to guarantee ordering before overwriting the lib. -/
target ix_rs_net pkg : FilePath := do
  let _ ← ix_rs.fetch
  let args ← cargoArgs (net := true)
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi"

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
