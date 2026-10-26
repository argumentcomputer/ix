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

/-- The main library, with Lake's default root: the module `Ix` (`Ix.lean`) and
its imports, not every module under `Ix/`. A module that `Ix.lean` does not
import, such as `Ix.Cert.Audit`, is built only by a target that imports it,
such as `IxTests`. Nothing the `ix-kernel` dependency or `IxSharingVerify` owns
is under the `Ix.` module root (their declaration namespaces are, their module
names are not), so this library never shadows them. Keep new modules of theirs
under their roots. -/
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

/-- The `twins` suite's fixtures (`Tests.Ix.Compile.Twins.Fixtures` and its
imports). `IxTests` builds them but does not import them: the suite imports
them at run time, so their deliberately refused presentations stay out of the
environment that the whole-environment suites compile. -/
lean_lib TwinsFixtures where
  roots := #[`Tests.Ix.Compile.Twins.Fixtures]

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true
  needs := #[`@/ix, `@/«kernel-check-ixe», `@/TwinsFixtures]
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

/-- Focused source-contract checks, including fresh-module registration export. -/
lean_exe «source-contract-tests» where
  root := `Tests.SourceContractMain
  supportInterpreter := true

/-- Focused Ixon v4 codec, locality, and cross-language transport checks;
`--export-fixtures` and `--export-handoff` regenerate the generated fixtures.
Scratch files live in `$IX_IXON_V4_DIR` (default `/tmp`); see `--help`. -/
lean_exe «ixon-v4-tests» where
  root := `Tests.IxonV4Main
  supportInterpreter := true
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

/-- Offline component-family traces; no production artifacts are emitted. -/
lean_exe «sharing-family-trace» where
  root := `Benchmarks.SharingFamilyTrace

/-- Offline captured-input normalization, using the proved production evaluator. -/
lean_exe «sharing-family-normalize» where
  root := `Benchmarks.SharingFamilyNormalize

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

/-- The Lean names whose address differs between two compiled environments,
grouped by block with a one-word cause (packaging, nested order, cascade,
content); `--originals` lists the regenerated auxiliaries whose
`Named.original` differs from their address: `ixe-diff <old.ixe> <new.ixe>
[--names] [--tsv <rows.tsv>]` (`Benchmarks/Canon/IxeDiff.lean`). -/
lean_exe «ixe-diff» where
  root := `Benchmarks.Canon.IxeDiff
  moreLinkObjs := #[ix_rs]

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

section ModuleCoverage

/-- Why the module-coverage gate does not build a `.lean` file under a covered
directory. -/
inductive ModuleExclusionKind where
  /-- A module that does not elaborate yet, with its first error under
  `lake build --wfail`. Remove the entry once the module builds. -/
  | draft (firstError : String)
  /-- A draft that fails only because it imports another draft. -/
  | importsDraft (draft : Lean.Name)
  /-- Not Lean to compile: input data for a tool. -/
  | data
  /-- A `lean --run` script under no library or executable root. -/
  | script
  /-- A source file a tool elaborates (an `ix compile` input), under no
  library or executable root. -/
  | compileInput
  /-- A reproducer Lean itself rejects, kept so that `suite`'s record is
  complete; the suite expects `firstError`. -/
  | rejectedFixture (suite : String) (firstError : String)

/-- A `.lean` file under a covered directory that `check-modules` leaves out. -/
structure ModuleExclusion where
  module : Lean.Name
  reason : String
  kind : ModuleExclusionKind

/-- The `.lean` files under `coveredDirs` that `check-modules` does not build.
It builds every other module there, so a new module is either built or listed
here. No module is a draft. -/
def moduleExclusions : Array ModuleExclusion := #[
  { module := `Tests.Fixtures.«trust-surface».lexer
    reason := "the trust-surface scanner's lexer self-test input, kept unchanged from con-leche"
    kind := .data },
  { module := `Benchmarks.Kernel.AnthropicFLT.RunSuite
    reason := "the FLT subject harness, run with `lean --run` (its README)"
    kind := .script },
  { module := `Benchmarks.Kernel.IxEnv
    reason := "`import Ix` as an `ix compile` input: the environment of Ix itself"
    kind := .compileInput },
  { module := `Tests.Ix.Compile.AuxCert.PropEvap
    reason := "WB §9 reproducer; nothing reaches either compiler"
    kind := .rejectedFixture "aux-cert" "Application type mismatch" },
  { module := `Tests.Ix.Compile.AuxCert.SortU
    reason := "WB-B8 note reproducer; nothing reaches either compiler"
    kind := .rejectedFixture "aux-cert" "Invalid universe polymorphic resulting type" },
  { module := `Tests.Ix.Compile.AuxCert.SortURec
    reason := "WB-B8 note reproducer; nothing reaches either compiler"
    kind := .rejectedFixture "aux-cert" "Invalid universe polymorphic resulting type" },
  { module := `Tests.Ix.Compile.AuxCert.SortUOpt
    reason := "WB-B8 note reproducer; nothing reaches either compiler"
    kind := .rejectedFixture "aux-cert" "Unknown constant `SortUOpt.SU.ctorIdx`" }]

/-- The directories whose modules `check-modules` builds, with the root files.
`IxC/` (its own package, globbed, `lake -d IxC build --wfail`) and
`IxSharingVerify/` (a globbed library, built by `lake lint`) are covered by
their own targets; `Models/` and every directory with its own lakefile are
other workspaces. -/
def coveredDirs : Array FilePath := #["Ix", "Tests", "Benchmarks", "Apps", "MultiStark"]
def coveredRootFiles : Array FilePath :=
  #["Ix.lean", "Main.lean", "Tests.lean", "Apps.lean", "MultiStark.lean"]

/-- Whether `dir` is a nested Lake workspace (it has its own lakefile). -/
def isNestedWorkspace (dir : FilePath) : IO Bool := do
  return (← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists)

/-- The modules of the `.lean` files under `dir` (relative to the package
root), skipping `.lake` directories and nested workspaces. -/
def modulesUnder (dir : FilePath) : IO (Array Lean.Name) := do
  let entries ← dir.walkDir fun d => do
    return d.fileName != some ".lake" && !(← isNestedWorkspace d)
  let modules := entries.filterMap fun path =>
    if path.extension == some "lean" then
      some <| (path.withExtension "").components.foldl .str .anonymous
    else none
  return modules.qsort (·.toString < ·.toString)

/-- Every module the gate covers, sorted. -/
def coveredModules : IO (Array Lean.Name) := do
  let mut out := #[]
  for d in coveredDirs do out := out ++ (← modulesUnder d)
  for f in coveredRootFiles do
    if ← f.pathExists then out := out.push (f.withExtension "").toString.toName
  return out.qsort (·.toString < ·.toString)

/-- The module-coverage gate: check `moduleExclusions`, require every covered
module to be buildable (under a library root or an executable root), then
`lake build <args> +M…` every covered module that is not excluded. -/
def checkModules (args : List String) : ScriptM UInt32 := do
  let ws ← getWorkspace
  let modules ← coveredModules
  let excluded := moduleExclusions.map (·.module)
  let drafts := moduleExclusions.filterMap fun e =>
    match e.kind with | .draft _ | .importsDraft _ => some e.module | _ => none
  let mut problems : Array String := #[]
  for e in moduleExclusions do
    unless modules.contains e.module do
      problems := problems.push s!"excluded {e.module} is not a module under the covered directories"
    if let .importsDraft d := e.kind then
      unless drafts.contains d do
        problems := problems.push s!"draft {e.module} imports {d}, which is not a draft"
  unless excluded.toList.eraseDups.length == excluded.size do
    problems := problems.push "moduleExclusions lists a module twice"
  let built := modules.filter (!excluded.contains ·)
  for m in built do
    if (ws.findTargetModule? m).isNone then
      problems := problems.push s!"{m} is under no library root or executable root: \
        add it to a library, or list it in moduleExclusions with its kind"
  unless problems.isEmpty do
    for p in problems do IO.eprintln s!"[check-modules] {p}"
    return 1
  IO.println s!"[check-modules] building {built.size} modules under \
    {coveredDirs.toList} and the root files; {excluded.size} left out: {excluded.toList}"
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["build"] ++ args.toArray ++ built.map (s!"+{·}")
    stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  return if code == 0 then 0 else 1

end ModuleCoverage

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
  IO.println "Building: every module under the covered directories (check-modules)"
  if (← checkModules args) != 0 then failed := failed.push "check-modules"
  if failed.isEmpty then return 0
  IO.eprintln s!"Failed to build {failed.size} of {allNames.length + 1} targets: {", ".intercalate failed.toList}"
  return 1

/-- The module-coverage gate (`checkModules`), always strict. `lake lint`
runs it too, with the lint arguments. -/
script "check-modules" (args) := do
  return ← checkModules ("--wfail" :: args)

end Scripts

section IxSharingVerify

/- Proofs of the canonical sharing construction (`Ix.Sharing`) and their
audits: `IxSharingVerify` and every module under `IxSharingVerify/`. They
declare the `Ix.Sharing.Verify` namespace, and the `Family*` modules extend
the production rule's namespace `Ix.Sharing.Family`. Not a default target;
`lake build IxSharingVerify` and `lake lint` build all of it. The module root
is outside `Ix.`, so the `Ix` library's root never claims these modules; the
runtime modules under `Ix.Sharing` belong to `Ix`. The dependency is not
one-way: the certification modules `Ix.CompileCert.SharingRoots` and
`Ix.CompileCert.WireTables` import `IxSharingVerify.{CanonicalMeaning,Builder,
BlockTables}`, so every target that builds them (for example `IxTests`) also
builds those proof modules and their imports. -/
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

/-- The Source-mode check (`Ix.LeanIngress`) on Lean environments loaded from
this toolchain's `.olean` files, group by group: the `lake test` fixture
(`--fixture`) or the given modules (`kernel-source-ingress Init Std`). -/
lean_exe «kernel-source-ingress» where
  root := `Tests.Ix.Kernel.SourceIngressMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- Step 6b's oracle: `.meta` and `.source` names against Lean's
(`Tests.Ix.Kernel.MetaNames`). -/
lean_exe «kernel-meta-names» where
  root := `Tests.Ix.Kernel.MetaNames
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- The certified checker's benchmark drivers and reporting helpers. -/
lean_lib KernelEntry where
  roots := #[`Benchmarks.Kernel.CheckIxeStep,
    `Benchmarks.Kernel.CheckIxeReadCache, `Benchmarks.Kernel.CheckIxeStream, `Benchmarks.Kernel.CheckIxePool,
    `Benchmarks.Kernel.CheckIxe, `Benchmarks.Kernel.CheckIxeFold, `Benchmarks.Kernel.CheckIxeEntry,
    `Benchmarks.Kernel.CheckIxeGuarded, `Benchmarks.Kernel.CheckIxeRows,
    `Benchmarks.Kernel.CheckIxeReport, `Benchmarks.Kernel.CheckIxePaired, `Benchmarks.Kernel.CheckIxeMeta]

/-- The certified checker's environment check over a compiled `.ixe`: the
verified checker through the Ixon reader, one row per constant (untrusted
step); the records streamed (`--load eager` decodes them all up front), and
with `--jobs <n>` the checks on a pool of `n` workers. -/
lean_exe «kernel-check-ixe» where
  root := `Benchmarks.Kernel.CheckIxeMain
  moreLinkObjs := #[ix_rs]

/-- The role-table generator: regenerates `IxC/Kernel/Ixon/RoleData.lean` (the
default role table, its evidence records and the Ixon prelude) from a compiled
Init (`.lake/envs/initstd.ixe`), each binding validated by the verified fold,
and Source mode's evidence from the certificate module's environment, which it
loads as `kernel-source-ingress` does (hence the interpreter). -/
lean_exe «kernel-pin-gen» where
  root := `Benchmarks.Kernel.PinGen
  supportInterpreter := true
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
  run "lake" #["build", "--wfail", "Ix.Ixon.Projection.Audit", "Ix.Ixon.BlockOrder.Audit", "Ix.Ixon.Authenticated.Audit", "Ix.Cert.RuntimeAudit", "Tests.Ix.Kernel.BlockOrder", "Tests.Ix.Kernel.AddressPure", "Tests.Ix.Kernel.Projection", "Tests.Ix.Kernel.Reader", "Tests.Ix.Kernel.CertifiedEntry", "Tests.Ix.Kernel.Authentication", "Tests.Ix.Kernel.Contracts", "Tests.Ix.Kernel.ReaderRoundtrip", "Tests.Ix.Kernel.Axioms", "Ix.SpecDigest", "Tests.Ix.Kernel.Erasure", "Tests.Ix.Kernel.DisplayRead"]
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
