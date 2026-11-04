import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"
  -- CUDA builds load their shared libraries from `.lake/build/lib`. Those
  -- resolve libc against the running system, whose glibc can be newer than
  -- Lean's link-time stubs; each library is itself linked with -z defs. The
  -- flags are unconditional because Lake does not re-elaborate this file when
  -- `IX_CUDA` changes, and they are inert without CUDA.
  moreLinkArgs := if System.Platform.isLinux then
    #["-Wl,--allow-shlib-undefined", "-Wl,-rpath,$ORIGIN/../lib"] else #[]

require aiur from "Aiur"
require ixvm from "IxVM"
require multiStark from "MultiStark"

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

Compression runs inside `ix`. Its final backends (`plonk`, `groth16`) are
compiled into `ix_rs_net` only, so other executables never build Go. With
`cuda`, the native libraries (multi-stark's, the BN254 KZG/PLONK library and,
for Groth16, ICICLE) are copied to `.lake/build/lib` and found through
`$ORIGIN/../lib`; each Rust archive target links them itself.

The `ix_rs_test` and `ix_rs_net` targets fetch `ix_rs` first to guarantee ordering
before Cargo overwrites its release archive, then snapshot distinct Lake artifacts.
The second Cargo build is incremental — only feature-affected crates recompile.

The archives are built when native targets need them. Keeping Rust linkage on
`Ix` keeps `ix_rs` out of the certified kernel's build.

Every archive contains the formal Aiur prover library (`ix-prover`), which the
`ix` CLI runs in process.
-/
section FFI

/-- Whether the environment variable `name` is `1`, `true` or `yes`. -/
def enabled (name : String) : IO Bool :=
  return (← IO.getEnv name) matches some "1" | some "true" | some "yes"

/-- Rust feature selection shared by compilation and native runtime linkage.
IX_NO_PAR=1 disables parallel; IX_CUDA enables CUDA; IX_CUDA_TRACE_CODEGEN
enables generated trace kernels and implies CUDA. For `net` (the `ix` CLI),
IX_PLONK and IX_GROTH16 add those final compression backends, which otherwise
end at the recursive KZG proof; with CUDA, Groth16 links an installed ICICLE
library. -/
def cargoFeatures (testFfi : Bool := false) (net : Bool := false) : IO (Array String) := do
  let mut features := #[]
  if net && (← enabled "IX_PLONK") then features := features.push "plonk"
  if net && (← enabled "IX_GROTH16") then features := features.push "groth16"
  if (← IO.getEnv "IX_NO_PAR") != some "1" then features := features.push "parallel"
  if ← enabled "IX_CUDA" then features := features.push "cuda"
  if ← enabled "IX_CUDA_TRACE_CODEGEN" then features := features.push "cuda-trace-codegen"
  if net && !System.Platform.isOSX then features := features.push "net"
  if testFfi then features := features.push "test-ffi"
  return features

/-- Build args for `cargo build --release` with opt-in feature overrides.
Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) (net : Bool := false) : IO (Array String) := do
  let features ← cargoFeatures testFfi net
  IO.println s!"Ix Rust features: {if features.isEmpty then "none" else ",".intercalate features.toList}"
  let buildArgs := #["build", "--release", "-p", "ix-ffi"]
  if features.isEmpty then return buildArgs
  else return buildArgs ++ #["--features", ",".intercalate features.toList]

/-- The shared libraries the build scripts report (`IX_RUNTIME_ARTIFACTS`):
each `source` is copied to `lib/<path>`, keeping ICICLE's backend plugins at
the relative paths it loads them from, and the `link` ones are linked. -/
def cargoRuntimeArtifacts (messages : String) :
    Except String (Array (FilePath × String × Bool)) := do
  let mut artifacts := #[]
  for line in messages.splitOn "\n" do
    let .ok message := Lean.Json.parse line | continue
    let .ok variables := message.getObjValAs? (Array (Array String)) "env" | continue
    for entry in variables do
      if entry.size == 2 && entry[0]! == "IX_RUNTIME_ARTIFACTS" then
        let entries ← (← Lean.Json.parse entry[1]!).getArr?
        for artifact in entries do
          artifacts := artifacts.push (FilePath.mk (← artifact.getObjValAs? String "source"),
            ← artifact.getObjValAs? String "path", ← artifact.getObjValAs? Bool "link")
  return artifacts

/-- Copy `source` to `output` with its modification time, unless an identical
copy is already there. Replacing the inode keeps an already-loaded shared
library intact. -/
def snapshot (source output : FilePath) : IO Unit := do
  if ← output.pathExists then
    let (old, new) := (← output.metadata, ← source.metadata)
    if old.modified == new.modified && old.byteSize == new.byteSize then return
  IO.FS.createDirAll output.parent.get!
  let temporary := output.addExtension "tmp"
  discard <| IO.Process.run { cmd := "cp", args := #["-p", source.toString, temporary.toString] }
  IO.FS.rename temporary output

/-- The libraries recorded beside a Rust archive: whether each is linked, and
its path relative to `lib/`. -/
def runtimeArtifacts (archive : FilePath) : IO (Array (Bool × String)) := do
  let lines := (← IO.FS.lines (archive.withExtension "runtime")).filter (!·.isEmpty)
  lines.mapM fun line => match line.splitOn " " with
    | ["link", path] => pure (true, path)
    | ["load", path] => pure (false, path)
    | _ => throw <| IO.userError s!"malformed runtime manifest line: {line}"

/-- One feature selection of the Rust static lib, as a target links it. Cargo
runs on every build and decides what is stale; the archive is snapshotted to
`lib/libix_ffi_{tag}.a`, so targets relink only when its contents change.
A static archive does not carry its shared-library dependencies to Lean's
linker, so with CUDA this is an `ld` script naming the archive together with
the libraries the build scripts report. -/
def buildRustStatic (pkg : Package) (args : Array String) (tag : String)
    (before : Option (Job FilePath) := none) : FetchM (Job FilePath) := do
  let start := match before with
    | some before => before.map fun _ => ()
    | none => Job.nil
  start.mapM fun _ => do
    let result ← captureProc' {
      cmd := "cargo"
      args := args.push "--message-format=json-render-diagnostics"
      cwd := pkg.dir
    }
    unless result.stderr.isEmpty do logVerbose result.stderr
    let artifacts ← match cargoRuntimeArtifacts result.stdout with
      | .ok artifacts => pure artifacts
      | .error message => error message
    let lib := pkg.buildDir / "lib"
    for (source, path, _) in artifacts do
      snapshot source (lib / FilePath.mk path)
    let archive := lib / s!"libix_ffi_{tag}.a"
    snapshot (pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi") archive
    -- One `link <path>` or `load <path>` line per library, relative to `lib/`.
    IO.FS.writeFile (archive.withExtension "runtime") <| String.join <|
      artifacts.toList.map fun (_, path, link) => s!"{if link then "link" else "load"} {path}\n"
    setTrace (← computeTrace archive)
    let linked := artifacts.filterMap fun (_, path, link) => if link then some path else none
    if linked.isEmpty then return archive
    let ldScript := lib / s!"libix_ffi_{tag}_link.so"
    let paths := #[archive.toString] ++ linked.map fun path => (lib / FilePath.mk path).toString
    IO.FS.writeFile ldScript s!"INPUT({" ".intercalate paths.toList})\n"
    addTrace (← computeTrace ldScript)
    return ldScript

/-- Build the Rust static lib with default features (`parallel`). -/
target ix_rs pkg : FilePath := do
  buildRustStatic pkg (← cargoArgs) "default"

/-- Cargo feature variants run after the default build, since every
selection writes Cargo's one release archive. -/
target ix_rs_test pkg : FilePath := do
  buildRustStatic pkg (← cargoArgs (testFfi := true)) "test" (some (← ix_rs.fetch))

/-- Build the Rust static lib with `net` for the `ix` CLI. -/
target ix_rs_net pkg : FilePath := do
  buildRustStatic pkg (← cargoArgs (net := true)) "net" (some (← ix_rs.fetch))

end FFI

/-- `lake -R -Kprofile build` compiles with frame pointers, so `perf` can unwind
call graphs through generated C (LBR and DWARF unwinding are unavailable on
the benchmark machines). The default build is unaffected. -/
def profileLeancArgs : Array String :=
  if (get_config? profile).isSome then #["-fno-omit-frame-pointer"] else #[]

/-- The main library, with Lake's default root: the module `Ix` (`Ix.lean`) and
its imports, not every module under `Ix/`. A module that `Ix.lean` does not
import, such as `Ix.Cert.Audit`, is built only when named, as the
`check-kernel` gate and `lake lint`'s module coverage name it. Nothing the `ix-kernel` dependency or `IxSharingVerify` owns
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

/-- The certified entry's host cases (`Tests.Ix.Kernel.EntryCaseDefs`), built as a
library of their own so that suites can import them at run time (some host cases
are installed unchecked on purpose). -/
lean_lib EntryCaseFixtures where
  roots := #[`Tests.Ix.Kernel.EntryCaseDefs]

lean_exe «formal-aiur-tests» where
  root := `Tests.FormalAiur
  supportInterpreter := true

/-- Differential checks and measurements of the direct compiler handoff. -/
lean_exe «formal-image-tests» where
  root := `Tests.FormalImage
  supportInterpreter := true

lean_exe «formal-aggregate-tests» where
  root := `Tests.FormalAggregate
  supportInterpreter := true

/-- Fingerprint of the formal verify path; `tools/check-verify-path.sh`
compares it with the pinned `tools/verify-path.fingerprint`. -/
lean_exe «verify-path» where
  root := `Tests.VerifyPath
  supportInterpreter := true

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true
  needs := #[`@/ix, `@/«kernel-check-ixe», `@/EntryCaseFixtures]
  moreLinkObjs := #[ix_rs_test]

/-- The FFI suite (`IxTests ffi`) on its own, linked like `IxTests` with the
test-only FFI code, for the merge queue's Valgrind job: its import closure is
the host library's, without the test binary's proofs. -/
lean_exe «ffi-tests» where
  root := `Tests.FFIMain
  moreLinkObjs := #[ix_rs_test]

lean_exe «arena-exclude» where
  root := `Tests.Ix.Kernel.ArenaExclude
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

/-- Fixed component work with independently scaled full-DAG scratch buffers. -/
lean_exe «sharing-scratch» where
  root := `Benchmarks.SharingScratch

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
content): `ixe-diff <old.ixe> <new.ixe> [--names] [--tsv <rows.tsv>]`
(`Benchmarks/Canon/IxeDiff.lean`). -/
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
  { module := `Tests.Fixtures.toolchains.«Certs-4.35.0»
    reason := "the certificate theorems for Lean 4.35.0, compiled by that toolchain's own `lean` when the toolchain fixtures are regenerated; it does not elaborate on ix's toolchain"
    kind := .data },
  { module := `Tests.Fixtures.toolchains.Regenerate
    reason := "the toolchain fixtures' regeneration recipe, run with `lean --run`"
    kind := .script }]

/-- The directories whose modules `check-modules` builds, with the root files.
`IxC/` (its own package, globbed, `lake -d IxC build --wfail`) and
`IxSharingVerify/` (a globbed library, built by `lake lint`) are covered by
their own targets; `Models/` and every directory with its own lakefile are
other workspaces. -/
def coveredDirs : Array FilePath := #["Ix", "Tests", "Benchmarks", "Apps"]
def coveredRootFiles : Array FilePath :=
  #["Ix.lean", "Main.lean", "Tests.lean", "Apps.lean"]

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

  let fullAccess := { read := true, write := true, execution := true }
  let noWriteAccess := { fullAccess with write := false }
  let fileRight := { user := fullAccess, group := fullAccess, other := noWriteAccess }
  FS.createDirAll binDir
  let destination := binDir / "ix"
  FS.writeBinFile destination (← FS.readBinFile $ ".lake" / "build" / "bin" / "ix")
  setAccessRights destination fileRight
  let libraryDir := binDir.parent.getD "." / "lib"
  for (_, name) in ← runtimeArtifacts (".lake" / "build" / "lib" / "libix_ffi_net.a") do
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
  IO.println "Building: every module under the covered directories (check-modules)"
  if (← checkModules args) != 0 then failed := failed.push "check-modules"
  IO.println "Checking: source terminology (check-source-docs)"
  let hygiene ← IO.Process.spawn {
    cmd := "lake", args := #["env", "lean", "--run", "Scripts/SourceHygiene.lean"]
    stdout := .inherit, stderr := .inherit }
  if (← hygiene.wait) != 0 then failed := failed.push "check-source-docs"
  if failed.isEmpty then return 0
  IO.eprintln s!"Failed {failed.size} of {allNames.length + 2} build and lint checks: {", ".intercalate failed.toList}"
  return 1

/-- Reject retired compiler APIs and private planning references in source
and documentation. The scanner has no grandfather baseline. -/
script "check-source-docs" := do
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["env", "lean", "--run", "Scripts/SourceHygiene.lean"]
    stdout := .inherit, stderr := .inherit }
  return ← child.wait

/-- The module-coverage gate (`checkModules`), always strict. `lake lint`
runs it too, with the lint arguments. -/
script "check-modules" (args) := do
  return ← checkModules ("--wfail" :: args)

/-- Check the `IxTests` registry against CI workflows and required entries. -/
script "check-ixtests-registry" := do
  let child ← IO.Process.spawn {
    cmd := ".lake/build/bin/IxTests", args := #["ixtests-registry"]
    stdout := .inherit, stderr := .inherit }
  return ← child.wait

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

/-- Host-compiled Lean declarations through the certified entry
`Ix.Kernel.Admission.checkBytes`, each with an exact expected verdict. -/
lean_exe «kernel-entry-cases» where
  root := `Tests.Ix.Kernel.EntryCases
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- The Ixon reader against a direct translation of Lean's constants over
`Init` and `Std` (`Tests/Ix/Kernel/ReaderFidelity.lean`): the compiled environment
(`kernel-reader-fidelity .lake/envs/initstd.ixe [limit]`), `Init` and `Std`
compiled in process (`--compile [limit]`), bounded prefix check
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

/-- Oracle comparing `.meta` and `.source` names against Lean's
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
the host-side tests, optionally the set-theory model, the certification
statements' freeze (`Ix.Cert.Audit`), the layering and
trust-surface fences, the certified entry's host-compiled
cases, and the `.meta` and `.source` names against Lean's. -/
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
  run "lake" #["build", "--wfail", "Ix.Ixon.Projection.Audit", "Ix.Ixon.BlockOrder.Audit", "Ix.Ixon.Authenticated.Audit", "Ix.Cert.RuntimeAudit", "Ix.Cert.ModuleAudit", "Tests.Ix.Kernel.BlockOrder", "Tests.Ix.Kernel.AddressPure", "Tests.Ix.Kernel.Projection", "Tests.Ix.Kernel.Reader", "Tests.Ix.Kernel.CertifiedEntry", "Tests.Ix.Kernel.Authentication", "Tests.Ix.Kernel.Contracts", "Tests.Ix.Kernel.Axioms", "Ix.SpecDigest", "Tests.Ix.Kernel.Erasure"]
  if args == ["--with-model"] then
    run "lake" #["-d", "Models/SetTheory", "build", "--wfail"]
  -- The certification statements' freeze, which no test binary imports.
  run "lake" #["build", "--wfail", "Ix.Cert.Audit"]
  -- The kernel's fences, derived from con-leche's: import layering and the
  -- per-file escape allowlist, with the trust-surface lexer's self-test.
  run "lake" #["build", "--wfail", "kernel-layering", "kernel-trust-surface"]
  run ".lake/build/bin/kernel-layering" #[]
  run ".lake/build/bin/kernel-trust-surface" #[]
  -- Host-compiled Lean declarations through the certified entry, each with
  -- an exact expected verdict (`Tests/Ix/Kernel/EntryCases.lean`).
  run "lake" #["build", "--wfail", "kernel-entry-cases"]
  let entry ← IO.Process.output { cmd := ".lake/build/bin/kernel-entry-cases" }
  IO.FS.writeFile ".lake/build/kernel-entry-cases.jsonl" entry.stdout
  IO.eprint entry.stderr
  unless entry.exitCode == 0 do
    IO.eprint entry.stdout
    throw <| IO.userError "kernel-entry-cases failed; see .lake/build/kernel-entry-cases.jsonl"
  -- The `.meta` and `.source` names against Lean's, on ill-typed declarations
  -- and the fixtures (`Tests/Ix/Kernel/MetaNames.lean`).
  run "lake" #["build", "--wfail", "kernel-meta-names"]
  run ".lake/build/bin/kernel-meta-names" #[]
  IO.println "Certified kernel checks passed."
  return 0

end IxC
