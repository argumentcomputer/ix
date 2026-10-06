import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

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

The `ix_rs_test` and `ix_rs_net` targets fetch `ix_rs` first to guarantee ordering
before Cargo overwrites its release archive, then snapshot distinct Lake artifacts.
The second Cargo build is incremental — only feature-affected crates recompile.

The archives are built when native targets need them. Keeping Rust linkage on
`Ix` keeps `ix_rs` out of the certified kernel's build.
-/
section FFI

/-- Build args for `cargo build --release` with opt-in feature overrides.
Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) (net : Bool := false) : IO (Array String) := do
  -- IX_NO_PAR=1 disables parallel; IX_CUDA=1/true/yes enables CUDA;
  -- IX_CUDA_TRACE_CODEGEN=1 enables generated trace kernels and implies CUDA.
  let ixNoPar ← IO.getEnv "IX_NO_PAR"
  let ixCuda ← IO.getEnv "IX_CUDA"
  let ixTraceCodegen ← IO.getEnv "IX_CUDA_TRACE_CODEGEN"
  let mut features : Array String := #[]
  if ixNoPar != some "1" then features := features.push "parallel"
  if ixCuda == some "1" || ixCuda == some "true" || ixCuda == some "yes" then
    features := features.push "cuda"
  if ixTraceCodegen == some "1" || ixTraceCodegen == some "true" || ixTraceCodegen == some "yes" then
    features := features.push "cuda-trace-codegen"
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
    path.extension == some "rs" || path.extension == some "cu" ||
    path.extension == some "cuh" || path.extension == some "h" ||
    path.extension == some "hpp" || path.fileName == "Cargo.toml" ||
    path.fileName == "trace-manifest.json"
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
  moreLinkObjs := #[ix_rs_net]

section Tests

lean_lib Tests

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true
  needs := #[`@/ix, `@/«kernel-check-ixe»]
  moreLinkObjs := #[ix_rs_test]

/-- Focused compiler-certification checks, including native producer FFI. -/
lean_exe «compile-cert-c1» where
  root := `Tests.Ix.CompileCert.Run
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_test]

/-- The compiler certifier: a Lean environment and an `.ixe`, one verdict per
constant (certified, unsupported, blocked, rejected), through the certified
association check `Ix.CompileCert.checkIndexed` (`Ix/CompileCert/Certifier.lean`). -/
lean_exe «compile-certify» where
  root := `Ix.CompileCert.CertifierMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

lean_exe «arena-exclude» where
  root := `Tests.Ix.Kernel.ArenaExclude
  supportInterpreter := true

/-- Regenerates, or with `--check` verifies, the trace-codegen test fixtures:
the Rust writers, CUDA units and manifest the `aiur` parity tests compile
against. -/
lean_exe «trace-fixtures» where
  root := `Tests.Aiur.TraceFixtures
  supportInterpreter := true

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

/-- The canonicalisation census computed by Pass 1 (`Ix.Compile.Canon`) under
today's rules and the Phase A rules: `canon-census <source.lean> <stored.ixe>
[--tsv <blocks.tsv>]` (`Benchmarks/Canon/Census.lean`). -/
lean_exe «canon-census» where
  root := `Benchmarks.Canon.Census
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- Deterministic Phase A shape generation and explicit corpus oracle driver.
`lake exe aux-shape-sweep --help` lists generation, filtering, assembly and run
commands. Broad sweeps are explicit, never part of the default test runner. -/
lean_exe «aux-shape-sweep» where
  root := `Tests.Ix.Compile.Corpus.Main
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- Selected checker-support closure against whole compilation, with a raw
negative control and strict certified reports in both rewrite modes. -/
lean_exe «checker-support-regression» where
  root := `Tests.Ix.Compile.CheckerSupport.Main
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- The Lean names whose address differs between two compiled environments,
grouped by block with a one-word cause (packaging, nested order, cascade,
content); `--originals` lists the regenerated auxiliaries whose
`Named.original` differs from their address: `ixe-diff <old.ixe> <new.ixe>
[--names] [--tsv <rows.tsv>]` (`Benchmarks/Canon/IxeDiff.lean`). -/
lean_exe «ixe-diff» where
  root := `Benchmarks.Canon.IxeDiff
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

section CompileCert

/-- Run the compiler-certification lane's gate (`Ix/CompileCert`): the strict
build of its axiom audit `Ix.CompileCert.Audit` (the frozen root list, each
root within `propext`, `Classical.choice`, `Quot.sound`; the build prints the
audit's own `[cert-audit]` line); the strict build of `compile-cert-c1` and of
the test modules outside its closure, whose `#eval` and `#guard` controls run
at elaboration; then the fixture checks, under `lake env` (some import the
test modules' oleans): the self-contained `compile-cert-c1` modes and the test
modules with their own `main`. Each fails on a wrong verdict and prints its
own summary. `compiled` writes its producer output, which `projection-support`
and the certifier (`compile-certify` over the producer's cone, Lean side from
`Tests.Ix.CompileCert.BlockDefs`) then read. The runs over the stored Init+Std
and Mathlib environments need those artifacts and run by hand. -/
script "check-cert" (args) := do
  unless args.isEmpty do
    IO.eprintln "usage: lake run check-cert"
    return 2
  let run (cmd : String) (args : Array String) : ScriptM Unit := do
    let child ← IO.Process.spawn { cmd, args, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do
      throw <| IO.userError s!"{cmd} {args} failed with exit code {code}"
  let mainTests := #["HelperNames", "InstalledCaps", "InstalledFields", "InstalledRules",
    "SourceBasis", "Support"]
  let elabTests := #["AnnotEntry", "AnnotNatOps", "AnnotReduceOps", "AnnotSupport",
    "InstalledImage", "Telescope", "ValueReceipt"]
  run "lake" #["build", "--wfail", "Ix.CompileCert.Audit"]
  run "lake" (#["build", "--wfail", "compile-cert-c1", "compile-certify"] ++
    (mainTests ++ elabTests).map (s!"+Tests.Ix.CompileCert.{·}"))
  let outDir := ".lake/build/compile-cert"
  IO.FS.createDirAll outDir
  let exe := ".lake/build/bin/compile-cert-c1"
  let checks : Array (String × Array String) :=
    #["direct", "blocks", "groups", "universes", "expressions", "source-install",
      "source-models", "source-normalized", "source-coverage", "source-projection-semantics", "indexed",
      "projection-lowering", "strong",
      "compiled"].map (fun mode => (mode, #[exe, mode])) ++
    #[("projection-support", #[exe, "projection-support", s!"{outDir}/compiled.ixe"]),
      ("certify", #[".lake/build/bin/compile-certify", "--modules", "Tests.Ix.CompileCert.BlockDefs",
        s!"{outDir}/compiled.ixe", s!"{outDir}/certify"]),
      ("certify-strong", #[".lake/build/bin/compile-certify", "--modules", "Tests.Ix.CompileCert.BlockDefs",
        s!"{outDir}/compiled.ixe", s!"{outDir}/certify-strong", "--strong"])] ++
    mainTests.map (fun test => (test, #["lean", "--run", s!"Tests/Ix/CompileCert/{test}.lean"]))
  for (name, checkArgs) in checks do
    let out ← IO.Process.output {
      cmd := "lake", args := #["env"] ++ checkArgs
      env := #[("C1_OUTPUT_DIR", some outDir)] }
    IO.FS.writeFile s!"{outDir}/{name}.log" (out.stdout ++ out.stderr)
    IO.eprint out.stderr
    unless out.exitCode == 0 do
      IO.eprint out.stdout
      throw <| IO.userError s!"compile-cert check {name} failed; see {outDir}/{name}.log"
    let lines := (out.stdout.splitOn "\n").filter (· ≠ "")
    let some summary := lines.getLast?
      | throw <| IO.userError s!"compile-cert check {name} printed nothing"
    IO.println s!"[check-cert] {name}: {summary}"
  IO.println "Compiler-certification checks passed."
  return 0

end CompileCert
