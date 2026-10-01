import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "369c09df268d7077dfea04a136abbd168351a6b4"

/- The pinned package supplies the pure Lean hash and host C/Rust
accelerators. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "c32002eeed36c520dfb73de32ef53483652e3aa5"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.34.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.34.0"

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
Used by `IxTests` and the focused `kernel-codec` differential runner.
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

end FFI

lean_lib MultiStark where
  moreLinkObjs := #[ix_rs]

/-- `lake build -K profile` compiles with frame pointers, so `perf` can unwind
call graphs through generated C (LBR and DWARF unwinding are unavailable on
the census machines). The default build is unaffected. -/
def profileLeancArgs : Array String :=
  if (get_config? profile).isSome then #["-fno-omit-frame-pointer"] else #[]

@[default_target]
lean_lib Ix where
  moreLinkObjs := #[ix_rs]
  moreLeancArgs := profileLeancArgs
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

/-- Focused source-contract checks, including fresh-module registration export. -/
lean_exe «source-contract-tests» where
  root := `Tests.SourceContractMain
  supportInterpreter := true

/-- Focused v3 codec, locality, and cross-language transport checks. -/
lean_exe «ixon-v3-tests» where
  root := `Tests.IxonV3Main
  moreLinkObjs := #[ix_rs_test]

/-- Regenerate format-specific primitive identities from the installed Lean environment. -/
lean_exe «ixon-v3-primitives» where
  root := `Tests.IxonV3Primitives
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_test]

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
  let allNames := (libNames ++ exeNames).toList
  for name in allNames do
    IO.println s!"Building: {name}"
    let child ← IO.Process.spawn {
      cmd := "lake", args := #["build", name] ++ args
      stdout := .inherit, stderr := .inherit }
    let exitCode ← child.wait
    if exitCode != 0 then return exitCode
  return 0

end Scripts

section IxKernelVendored

/-- The vendored con-leche modules under `Ix/Kernel`: every module there except
Ix's boundary (`Ref`, `Search`, `Audit`, `Ingress`, `Egress`, `Ixon`), one glob
per top-level entry (`scripts/vendor-conleche.py lake-globs`). -/
def vendoredKernelGlobs : Array Glob := #[
  -- BEGIN vendored kernel modules (scripts/vendor-conleche.py check-lake)
  .andSubmodules `Ix.Kernel.Basis, .one `Ix.Kernel.BasisA, .one `Ix.Kernel.BasisGen,
  .submodules `Ix.Kernel.Cached, .one `Ix.Kernel.Canon, .one `Ix.Kernel.Checker,
  .one `Ix.Kernel.CheckerBase, .one `Ix.Kernel.CheckerSplit, .one `Ix.Kernel.Core,
  .one `Ix.Kernel.CoreDefs, .one `Ix.Kernel.CoreIO, .one `Ix.Kernel.DeclCheck,
  .one `Ix.Kernel.Denotes, .one `Ix.Kernel.Env, .one `Ix.Kernel.Exclusive, .one `Ix.Kernel.Expr,
  .one `Ix.Kernel.ExprOps, .one `Ix.Kernel.FEnv, .submodules `Ix.Kernel.Frontend,
  .submodules `Ix.Kernel.Inductives, .one `Ix.Kernel.Level, .one `Ix.Kernel.LevelGeran,
  .one `Ix.Kernel.MainTheorem, .submodules `Ix.Kernel.Model, .one `Ix.Kernel.Name,
  .one `Ix.Kernel.NatOpPinSet, .submodules `Ix.Kernel.PinGen, .one `Ix.Kernel.PropRead,
  .one `Ix.Kernel.PropWhen, .submodules `Ix.Kernel.Rules, .submodules `Ix.Kernel.Semantics,
  .submodules `Ix.Kernel.SetModel, .submodules `Ix.Kernel.SetTheory, .one `Ix.Kernel.StdAxioms,
  .submodules `Ix.Kernel.Term, .one `Ix.Kernel.TrustAxioms, .one `Ix.Kernel.TrustPins,
  .one `Ix.Kernel.TypeChecker, .submodules `Ix.Kernel.Verify
  -- END vendored kernel modules
]

/- Con-leche's verified checker, vendored in place under `Ix/Kernel/**` with
namespace `Ix.Kernel` (`docs/kernel.md`, "Vendored con-leche"): the import
closure of `Ix.Kernel.model_exists` from
`https://github.com/leanprover/con-leche.git` at
`ae0c0c4e4ce6a0081648aff03fe9c39d002c4526` (Apache-2.0; the seven files of
upstream task #323 at `3ca9e2fe`). Every file is upstream's, rewritten by
`scripts/vendor-conleche.py` (paths and namespace `ConLeche` → `Ix.Kernel`),
except seven adapted ones and two Ix-authored modules
(`Ix/Kernel/{,Verify/}LevelGeran.lean`); `Tests/Ix/Kernel/ImportManifest.lean`
records each (`docs/kernel.md`, "Provenance"). Upstream's
`ConLeche/Kernel/NatOpPins.lean`, which splices upstream's JSON pin dumps, is
not vendored: Ix's Nat-operation pins are the Ixon-generated
`Ix/Kernel/Ixon/NatOpPinData.lean`.

The vendored modules are a library of their own for one option:
`linter.deprecated` is off, so the upstream sources, written for Lean 4.33.0,
build under `--wfail` on 4.34.0 without renaming deprecated lemmas. Lake
options are per library, and Ix's own modules under `Ix/Kernel` stay in `Ix`
with the default linters. Lake gives a module to the last-declared library
that can build it, and `Ix` (above) can build every `Ix.*` module, so this
library must stay below `Ix`, and its globs must be exactly the vendored tree
(a module they miss would be built by `Ix`): `scripts/vendor-conleche.py
check-lake`, in `check-kernel`, compares them with the tree. Not a default
target; `IxKernel/lakefile.lean` declares the same library. -/
lean_lib IxKernelVendored where
  roots := #[`Ix.Kernel.MainTheorem]
  globs := vendoredKernelGlobs
  leanOptions := #[⟨`linter.deprecated, false⟩]

end IxKernelVendored

section IxKernel

/- The certified kernel, `Ix.Kernel`, lives in this repository's `Ix/` tree but
is built for certification by the separate `IxKernel/` package, which reads the
same sources with no dependencies beyond the Lean toolchain:
`lake -d IxKernel build --wfail` is the strict gate. The root package builds the
same modules for its host consumers through the `Ix` library. See
`plans/ix-certified-roadmap.md`. -/

/- Provenance check for the kernel, the vendored con-leche tree among it: file
inventory, exact content hashes, vendor and port headers, licences, and
license files, against `Tests/Ix/Kernel/ImportManifest.lean`. Pass
`--source <old-ix-workspace>` (jj) and `--source-git plans/refs/con-leche`
(git) to also verify the recorded source hashes and re-derive every vendored
file from upstream through `scripts/vendor-conleche.py`. -/
lean_exe «kernel-provenance» where
  root := `Tests.Ix.Kernel.Provenance

lean_exe «kernel-codec» where
  root := `Tests.Ix.Kernel.CodecHost
  moreLinkObjs := #[ix_rs_test]

lean_exe «kernel-order» where
  root := `Tests.Ix.Kernel.BlockOrderHost
  moreLinkObjs := #[ix_rs_test]

/-- Host-compiled Lean declarations through the certified entry
`Ix.Ixon.Admission.checkBytes`, each with an exact expected verdict. -/
lean_exe «kernel-entry-cases» where
  root := `Tests.Ix.Kernel.EntryCases
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- Con-leche's universe-level comparison (`Level.leq`, `Level.isEquiv`, and
its Géran fallback `Level.Geran.leq`) against brute-force evaluation, on
random levels and on Ixon's canonical forms (cl-level). -/
lean_exe «conleche-level-differential» where
  root := `Tests.Ix.Kernel.ConLecheLevels
  moreLinkObjs := #[ix_rs]

/-- The Ixon reader against a direct translation of Lean's constants over
`Init` and `Std` (`Tests/Ix/Kernel/ReaderFidelity.lean`): the census corpus
(`kernel-reader-fidelity .lake/census/initstd.ixe [limit]`), `Init` and `Std`
compiled in process (`--compile [limit]`), `check-kernel`'s run
(`--check-kernel`) or the `lake test` fixture (`--fixture`). -/
lean_exe «kernel-reader-fidelity» where
  root := `Tests.Ix.Kernel.ReaderFidelityMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- Con-leche's verified checker through the Ixon reader: the
`checkBytes`-shaped entry and its per-record census (untrusted). -/
lean_lib KernelConLeche where
  roots := #[`Ix.Ixon.ConLecheAdmission, `Ix.Ixon.ConLecheConsistency, `Ix.Ixon.Consistency,
    `Benchmarks.Kernel.ConLecheStep,
    `Benchmarks.Kernel.ConLecheReadCache, `Benchmarks.Kernel.ConLecheCensus, `Benchmarks.Kernel.ConLecheFold]

/-- The certified checker's census (L5: the default census target):
con-leche through the Ixon reader, one row per record (untrusted step). -/
lean_exe «kernel-census» where
  root := `Benchmarks.Kernel.CensusCertifiedMain
  moreLinkObjs := #[ix_rs]

/-- The same driver under its L4 name, for existing scripts (Lake needs a
distinct root module per executable). -/
lean_exe «kernel-census-cl» where
  root := `Benchmarks.Kernel.ConLecheCensusMain
  moreLinkObjs := #[ix_rs]

/-- `kernel-census` with driver-side optimization switches (load mode,
worker-thread lane, persistent mark, two-phase pool), for measurement only
(`Benchmarks.Kernel.ConLecheOpt`, untrusted; `plans/review/cl-opt/`). -/
lean_exe «kernel-census-opt» where
  root := `Benchmarks.Kernel.ConLecheOpt
  moreLinkObjs := #[ix_rs]

/-- Regenerates `Ix/Kernel/Ixon/PinData.lean` (pins and prelude) from a
compiled Init (`.lake/census/initstd.ixe`), verified by con-leche. -/
lean_exe «conleche-pin-gen» where
  root := `Benchmarks.Kernel.ConLechePinGen
  moreLinkObjs := #[ix_rs]

/-- Run the certified kernel gate: the standalone strict build with its audits,
the host-side tests, provenance, the vendored tree's layering and
trust-surface fences, the certified entry's host-compiled cases, and the
reader's fidelity against Lean (the fixture closure and the first records of Init
and Std). -/
script "check-kernel" (args) := do
  unless args.isEmpty || args == ["--with-model"] do
    IO.eprintln "usage: lake run check-kernel [--with-model]"
    return 2
  let run (cmd : String) (args : Array String) : ScriptM Unit := do
    let child ← IO.Process.spawn { cmd, args, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do
      throw <| IO.userError s!"{cmd} {args} failed with exit code {code}"
  run "python3" #["scripts/check-kernel-retirement.py"]
  -- the vendored library's globs are exactly the vendored tree
  run "python3" #["scripts/vendor-conleche.py", "check-lake", "lakefile.lean", "IxKernel/lakefile.lean"]
  run "lake" #["-d", "IxKernel", "build", "--wfail"]
  run "lake" #["build", "--wfail", "kernel-provenance", "Ix.Ixon.ProjectionAudit", "Ix.Ixon.BlockOrderAudit", "Tests.Ix.Kernel.BlockOrder", "Tests.Ix.Kernel.AddressPure", "Tests.Ix.Kernel.Projection", "Tests.Ix.Kernel.IxonFixtures", "Tests.Ix.Kernel.Codec", "Tests.Ix.Kernel.ByteAdmission", "Tests.Ix.Kernel.ParserWork", "Tests.Ix.Kernel.ConLecheReader", "Tests.Ix.Kernel.CertifiedEntry", "Tests.Ix.Kernel.ConLecheRoundtrip", "Tests.Ix.Kernel.Axioms"]
  run ".lake/build/bin/kernel-provenance" #[]
  run "lake" #["build", "--wfail", "kernel-codec", "kernel-order"]
  let codec ← IO.Process.output { cmd := ".lake/build/bin/kernel-codec" }
  IO.FS.writeFile ".lake/build/kernel-codec.log" (codec.stdout ++ codec.stderr)
  IO.eprint codec.stderr
  unless codec.exitCode == 0 do
    throw <| IO.userError "kernel-codec failed; see .lake/build/kernel-codec.log"
  IO.println "Production Ixon codec and Rust differential checks passed."
  let order ← IO.Process.output { cmd := ".lake/build/bin/kernel-order" }
  IO.FS.writeFile ".lake/build/kernel-order.jsonl" order.stdout
  IO.eprint order.stderr
  unless order.exitCode == 0 do
    throw <| IO.userError "kernel-order failed; see .lake/build/kernel-order.jsonl"
  if args == ["--with-model"] then
    run "lake" #["-d", "Models/SetTheory", "build", "--wfail"]
  -- Con-leche's fences for the vendored tree (`scripts/vendor-conleche.py
  -- list`): import layering and the per-file escape allowlist, with the
  -- trust-surface lexer's self-test.
  run "bash" #["scripts/layering.sh"]
  run "bash" #["scripts/trust-surface.sh"]
  -- Host-compiled Lean declarations through the certified entry, each with
  -- an exact expected verdict (`Tests/Ix/Kernel/EntryCases.lean`).
  -- Con-leche's level comparison against brute-force evaluation (cl-level).
  run "lake" #["build", "--wfail", "conleche-level-differential"]
  run ".lake/build/bin/conleche-level-differential" #[]
  run "lake" #["build", "--wfail", "kernel-entry-cases"]
  let entry ← IO.Process.output { cmd := ".lake/build/bin/kernel-entry-cases" }
  IO.FS.writeFile ".lake/build/kernel-entry-cases.jsonl" entry.stdout
  IO.eprint entry.stderr
  unless entry.exitCode == 0 do
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
      throw <| IO.userError s!"kernel-reader-fidelity {mode} failed; see .lake/build/kernel-reader-fidelity.log"
  IO.println "Reader fidelity checks passed."
  IO.println "Certified kernel checks passed."
  return 0

end IxKernel
