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

require certifri from git
  "https://github.com/argumentcomputer/CertiFRI" @ "193e603b1643e0c29f3c8362075c094289940184"

require «certifri-proofs» from git
  "https://github.com/argumentcomputer/CertiFRI" @ "193e603b1643e0c29f3c8362075c094289940184" / "Proofs"

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

require «ix-ck» from "IxCK" with
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

Each Rust staticlib target traces its Rust sources, manifests and build env
vars via Lake so Cargo only runs when inputs change, and holds a workspace lock
around Cargo + snapshotting so concurrent variants never race on
`target/release/libix_ffi.a`.

The archives are built when native targets need them. Keeping Rust linkage on
`Ix` keeps `ix_rs` out of the certified kernel's build.

Every archive contains the formal Aiur prover library (`ix-prover`), which the
`ix` CLI runs in process. `ix_rs_net` also contains the native executors
generated from the certified programs (`formal_generated`): before Cargo runs,
`formal-codegen`, which links `ix_rs`, writes them as Rust source, and with
CUDA the trace writers as CUDA source, to `.lake/build/formal-generated`,
compiling the programs into the artifact cache (`.lake/aiur`) first when they
are missing (once per compiler and program revision; several minutes). An
executor only ever runs for the program with exactly its fingerprint, so a
stale one is never used.
-/
section FFI

/-- Whether the environment variable `name` is `1`, `true` or `yes`. -/
def enabled (name : String) : IO Bool :=
  return (← IO.getEnv name) matches some "1" | some "true" | some "yes"

/-- Whether the Rust archives are built with CUDA: IX_CUDA, or
IX_FORMAL_COMPILED_TRACE=1, which implies it. -/
def cudaEnabled : IO Bool := do
  return (← enabled "IX_CUDA") || (← IO.getEnv "IX_FORMAL_COMPILED_TRACE") == some "1"

/-- Whether `ix` links the native executors generated from the certified
programs (`formal_generated`). -/
def nativeExecutors : Bool := true

/-- Rust feature selection shared by compilation and native runtime linkage.
IX_NO_PAR=1 disables parallel; `cudaEnabled` enables CUDA. `native` links the
generated native executors (`formal_generated`), and with
IX_FORMAL_COMPILED_TRACE=1 also the generated CUDA trace writers of formal
IxVM (`AIUR_GPU_TRACE=compiled`). For `net` (the `ix` CLI), IX_PLONK and
IX_GROTH16 add those final compression backends, which otherwise end at the
recursive KZG proof; with CUDA, Groth16 links an installed ICICLE library. -/
def cargoFeatures (testFfi : Bool := false) (net : Bool := false) (native : Bool := false) :
    IO (Array String) := do
  let mut features := #[]
  if net && (← enabled "IX_PLONK") then features := features.push "plonk"
  if net && (← enabled "IX_GROTH16") then features := features.push "groth16"
  if (← IO.getEnv "IX_NO_PAR") != some "1" then features := features.push "parallel"
  if ← cudaEnabled then features := features.push "cuda"
  if native then
    features := features.push "native-executors"
    if (← IO.getEnv "IX_FORMAL_COMPILED_TRACE") == some "1" then
      features := features.push "formal-compiled-trace"
  if net && !System.Platform.isOSX then features := features.push "net"
  if testFfi then features := features.push "test-ffi"
  return features

/-- Build args for `cargo build --release` with opt-in feature overrides.
Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) (net : Bool := false) (native : Bool := false) :
    IO (Array String) := do
  let features ← cargoFeatures testFfi net native
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

/-- Acquire an atomic directory lock before running Cargo against the shared
`target/release/libix_ffi.a` output, preventing races between `ix_rs`,
`ix_rs_test`, and `ix_rs_net` without requiring `flock` (works on Linux and
macOS). -/
private def acquireCargoLock (lockDir : FilePath) : IO Unit := do
  IO.FS.createDirAll lockDir.parent.get!
  let mut acquired := false
  while !acquired do
    try
      IO.FS.createDir lockDir
      acquired := true
    catch _ =>
      IO.sleep 100

private def releaseCargoLock (lockDir : FilePath) : IO Unit := do
  try IO.FS.removeDir lockDir catch _ => pure ()

def withCargoLock (lockDir : FilePath) (act : JobM α) : JobM α := do
  acquireCargoLock lockDir
  try
    act
  finally
    releaseCargoLock lockDir

/-- Whether a file under `crates/` can affect the `ix-ffi` static library. -/
def isRustBuildInput (path : FilePath) : Bool :=
  let comps := path.components
  !comps.contains "target" &&
    (path.fileName == some "Cargo.toml" ||
     match path.extension with
     | some "rs" | some "cu" | some "c" | some "cpp" | some "h" | some "json" | some "bin" | some "ixl" => true
     | _ => false)

/-- Input trace for `buildRustStatic`: Rust sources, manifests, CUDA/C sources,
embedded fixtures, and build-affecting environment variables. When none of these
change, Lake skips invoking Cargo altogether. -/
def rustInputDeps (pkg : Package) (features : Array String) : FetchM (Job Unit) := do
  -- Sandboxed Nix builds omit Rust sources and symlink Crane's prebuilt
  -- `target/release/libix_ffi.a`; trace the prebuilt archive directly.
  if !(← (pkg.dir / "Cargo.lock").pathExists) then
    let prebuilt ← inputBinFile (pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi")
    return prebuilt.map fun _ => ()
  let crates ← inputDir (pkg.dir / "crates") false isRustBuildInput
  let mut manifestJobs : Array (Job FilePath) := #[
    ← inputTextFile (pkg.dir / "Cargo.toml"),
    ← inputTextFile (pkg.dir / "Cargo.lock"),
    ← inputTextFile (pkg.dir / "rust-toolchain.toml")
  ]
  if ← (pkg.dir / ".cargo" / "config.toml").pathExists then
    manifestJobs := manifestJobs.push (← inputTextFile (pkg.dir / ".cargo" / "config.toml"))
  let manifests := Job.collectArray manifestJobs
  let deps := crates.zipWith (fun _ _ => ()) manifests
  let envVars := #["RUSTFLAGS", "CARGO_BUILD_RUSTFLAGS", "MULTI_STARK_CUDA_ARCHS",
    "LEAN_SYSROOT", "LIBCLANG_PATH", "CLANG_PATH", "IX_CUDA", "IX_NO_PAR",
    "IX_PLONK", "IX_GROTH16", "IX_FORMAL_COMPILED_TRACE"]
  let envVals ← envVars.mapM fun k => do return s!"{k}={(← IO.getEnv k).getD ""}"
  let envKey := s!"features={",".intercalate features.toList};target={System.Platform.target};" ++
    ";".intercalate envVals.toList
  deps.mapM fun _ => do
    addTrace (BuildTrace.ofHash (Hash.ofString envKey))
    pure ()

/-- One feature selection of the Rust static lib, as a target links it. Lake
traces the Rust sources, manifests and build env vars so Cargo only runs when
inputs change; when Cargo runs, an atomic lock serializes writes to Cargo's
shared `target/release/libix_ffi.a` before snapshotting to `lib/libix_ffi_{tag}.a`.
A static archive does not carry its shared-library dependencies to Lean's
linker, so with CUDA this is an `ld` script naming the archive together with
the libraries the build scripts report. -/
def buildRustStatic (pkg : Package) (features : Array String) (args : Array String)
    (tag : String) (extraDep : Option (Job FilePath) := none) : FetchM (Job FilePath) := do
  let lib := pkg.buildDir / "lib"
  let archive := lib / s!"libix_ffi_{tag}.a"
  let deps ← rustInputDeps pkg features
  let deps := match extraDep with
    | some dep => deps.zipWith (fun _ _ => ()) dep
    | none => deps
  let archiveJob ← buildFileAfterDep archive deps fun _ => do
    withCargoLock (pkg.buildDir / "cargo-ffi.lock") do
      let result ← captureProc' {
        cmd := "cargo"
        args := args.push "--message-format=json-render-diagnostics"
        cwd := pkg.dir
      }
      unless result.stderr.isEmpty do logVerbose result.stderr
      let artifacts ← match cargoRuntimeArtifacts result.stdout with
        | .ok artifacts => pure artifacts
        | .error message => error message
      for (source, path, _) in artifacts do
        snapshot source (lib / FilePath.mk path)
      snapshot (pkg.dir / "target" / "release" / nameToStaticLib "ix_ffi") archive
      -- One `link <path>` or `load <path>` line per library, relative to `lib/`.
      IO.FS.writeFile (archive.withExtension "runtime") <| String.join <|
        artifacts.toList.map fun (_, path, link) => s!"{if link then "link" else "load"} {path}\n"
      let linked := artifacts.filterMap fun (_, path, link) => if link then some path else none
      if !linked.isEmpty then
        let ldScript := lib / s!"libix_ffi_{tag}_link.so"
        let paths := #[archive.toString] ++ linked.map fun path => (lib / FilePath.mk path).toString
        IO.FS.writeFile ldScript s!"INPUT({" ".intercalate paths.toList})\n"
  archiveJob.mapM fun archive => do
    let runtimeFile := archive.withExtension "runtime"
    if !(← runtimeFile.pathExists) then return archive
    let entries ← runtimeArtifacts runtimeFile
    let linked := entries.filterMap fun (link, path) => if link then some path else none
    if linked.isEmpty then return archive
    let ldScript := lib / s!"libix_ffi_{tag}_link.so"
    addTrace (← computeTrace ldScript)
    return ldScript

/-- Build the Rust static lib with default features (`parallel`). -/
target ix_rs pkg : FilePath := do
  let features ← cargoFeatures
  buildRustStatic pkg features (← cargoArgs) "default"

/-- Build the Rust static lib with `test-ffi` for test executables. -/
target ix_rs_test pkg : FilePath := do
  let features ← cargoFeatures (testFfi := true)
  buildRustStatic pkg features (← cargoArgs (testFfi := true)) "test"

/-- Writes the generated sources of the certified programs for
`formal_generated`. It links `ix_rs`, which has no generated code. -/
lean_exe «formal-codegen» where
  root := `FormalCodegen

/-- The generated sources of the certified programs in
`.lake/build/formal-generated`: the native executors, and in a CUDA build
(`cudaEnabled`) the trace writers. `formal-codegen` writes them, compiling
programs missing from the artifact cache first; it reruns only when it (and so
the programs and compiler it links) or the CUDA selection changed, and rewrites
only files whose contents changed. A CPU build removes any CUDA output. -/
target formal_generated pkg : FilePath := do
  let codegen ← «formal-codegen».fetch
  let cuda ← cudaEnabled
  let directory := pkg.buildDir / "formal-generated"
  buildFileAfterDep (directory / "inputs") codegen (extraDepTrace := do
      let envKey := s!"cuda={cuda};compiledTrace={(← IO.getEnv "IX_FORMAL_COMPILED_TRACE").getD ""};" ++
        s!"aiur={(← IO.getEnv "IX_AIUR_ARTIFACT").getD ""};" ++
        s!"verifier={(← IO.getEnv "IX_VERIFIER_ARTIFACT").getD ""};" ++
        s!"aggr={(← IO.getEnv "IX_AGGR_ARTIFACT").getD ""}"
      return .ofHash (Hash.ofString envKey) s!"formal_generated: {envKey}") fun exe => do
    proc {
      cmd := exe.toString
      args := #[directory.toString] ++ (if cuda then #["--cuda"] else #[])
      cwd := pkg.dir
      env := #[("IX_ROOT", some pkg.dir.toString)]
    }
    let inputsPath := directory / "inputs"
    let mut files : Array FilePath := #[]
    if ← directory.pathExists then
      for entry in ← directory.walkDir do
        if entry != inputsPath && !(← entry.isDir) then
          files := files.push entry
    files := files.qsort (·.toString < ·.toString)
    let mut manifest := s!"cuda {cuda}\n"
    for f in files do
      let h := Hash.ofByteArray (← IO.FS.readBinFile f)
      manifest := manifest ++ s!"{f.toString} {h}\n"
    IO.FS.writeFile inputsPath manifest

/-- Build the Rust static lib with `net` for the `ix` CLI, with the native
executors generated from the certified programs. -/
target ix_rs_net pkg : FilePath := do
  let generated? ← if nativeExecutors then
      some <$> formal_generated.fetch
    else pure none
  let features ← cargoFeatures (net := true) (native := nativeExecutors)
  buildRustStatic pkg features (← cargoArgs (net := true) (native := nativeExecutors)) "net" generated?

end FFI

/-- `lake -R -Kprofile build` compiles with frame pointers, so `perf` can unwind
call graphs through generated C (LBR and DWARF unwinding are unavailable on
the benchmark machines). The default build is unaffected. -/
def profileLeancArgs : Array String :=
  if (get_config? profile).isSome then #["-fno-omit-frame-pointer"] else #[]

/-- The committed pins of the certified formal Aiur programs' identities
and verifying keys (`Scripts/CheckFormalKeys.lean`). -/
input_file formalAiurKeys where
  path := "tools/formal-aiur.keys"
  text := true

/-- The pins, embedded in the module `FormalAiurKeys`, which Lake rebuilds
whenever the pin file changes. -/
lean_lib FormalAiurKeys where
  needs := #[formalAiurKeys]

/-- The main library, with Lake's default root: the module `Ix` (`Ix.lean`) and
its imports, not every module under `Ix/`. A module that `Ix.lean` does not
import, such as `Ix.Cert.Audit`, is built only when named, as the
`check-kernel` gate and `lake lint`'s module coverage name it. Nothing the `ix-ck` dependency or `IxSharingVerify` owns
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

/-- FRI soundness estimates for a key's instance (`docs/stark-parameters.md`). -/
lean_exe «fri-security» where
  root := `Scripts.FriSecurity

section Tests

lean_lib Tests

/-- The certified entry's host cases (`Tests.Ix.Kernel.EntryCaseDefs`), built as a
library of their own so that suites can import them at run time (some host cases
are installed unchecked on purpose). -/
lean_lib EntryCaseFixtures where
  roots := #[`Tests.Ix.Kernel.EntryCaseDefs]

/-- The formal claim fixtures; with `image`, the differential checks and
measurements of the direct compiler handoff; with `pins`, acceptance against
the pinned verifying keys. -/
lean_exe «formal-aiur-tests» where
  root := `Tests.FormalAiur
  supportInterpreter := true

lean_exe «formal-aggregate-tests» where
  root := `Tests.FormalAggregate
  supportInterpreter := true

/-- The formal backend's check drivers (`controller`, `cuda`, `ranges`), run by
`Scripts/CheckFormal.lean`. -/
lean_exe «formal-checks» where
  root := `Tests.FormalChecks
/-- The pin file of the checkout's certified programs;
`Scripts/CheckFormalKeys.lean` compares it with `tools/formal-aiur.keys`. -/
lean_exe «formal-keys» where
  root := `Tests.FormalKeys
  supportInterpreter := true

/-- Formal-package checks (`instance-symbols`, `ixvm-source`, and formal-package
manual runners) that import the nested `Aiur`/`IxVM`/`MultiStark` proof packages
(and therefore Mathlib). Kept separate from `IxTests` so the Nix flake and
merge-test builds of `IxTests` do not pull in Mathlib. -/
lean_exe «formal-package-tests» where
  root := `Tests.FormalPackageMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true
  needs := #[`@/ix, `@/«kernel-check-ixe», `@/«kernel-depth-case», `@/EntryCaseFixtures]
  moreLinkObjs := #[ix_rs_test]

/-- IxVM circuit-verdict and FFT-pin test runner (`--tier ci:ixvm`,
`--tier ci:nightly-ixvm`, and opt-in manual sweeps). Kept separate from
`IxTests` so host-only builds do not compile or link the 22 IxVM test modules. -/
lean_exe IxVMTests where
  root := `Tests.IxVMMain
  supportInterpreter := true
  needs := #[`@/ix, `@/«kernel-check-ixe»]
  moreLinkObjs := #[ix_rs_test]

/-- Manual-only benchmark, corpus, and differential test runner. Kept separate
from `IxTests` and `IxVMTests` so PR CI builds skip manual-only corpus drivers
while `lake lint` continues to typecheck every module. -/
lean_exe IxManualTests where
  root := `Tests.ManualMain
  supportInterpreter := true
  needs := #[`@/ix, `@/«kernel-check-ixe»]
  moreLinkObjs := #[ix_rs_test]

/-- One case of the `kernel-depth` test (`kernel-depth-case NAME N`), in a
process of its own on the stack `LEAN_STACK_SIZE_KB` sets: a small binary,
so that each case starts in milliseconds. -/
lean_exe «kernel-depth-case» where
  root := `Tests.Ix.Kernel.DepthCaseMain
  moreLinkObjs := #[ix_rs]

/-- The FFI suite (`IxTests ffi`) on its own, linked like `IxTests` with the
test-only FFI code, for the Valgrind job: its import closure is
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

/-- Focused Ixon codec, locality, and cross-language transport checks;
`--export-fixtures` regenerates the generated text fixtures.
Scratch files live in `$IX_IXON_TEST_DIR` (default `/tmp`); see `--help`. -/
lean_exe «ixon-tests» where
  root := `Tests.IxonMain
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_test]

/-- Regenerate format-specific primitive identities from the installed Lean
environment, into `$IX_IXON_TEST_DIR` (default `/tmp`); see `--help`. -/
lean_exe «ixon-primitives» where
  root := `Tests.IxonPrimitives
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

/-- One constant's IxVM benchmark row: execution and, with `--mode prove`, its
aggregate proof and root verification, measured in one process
(`Benchmarks/IxVM.lean`). `ix bench run --backend ixvm` runs it per constant. -/
lean_exe «bench-ixvm» where
  root := `Benchmarks.IxVM
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_net]

lean_exe «bench-compile-init» where
  root := `Benchmarks.CompileInit

lean_exe «lean-sharing-prof» where
  root := `Benchmarks.LeanSharingProf

/-- Corpus measurement for canonical sharing (`docs/sharing-minimum.md`):
expands every stored sharing table in an `.ixe`, checks the production
rebuild and reports subterm, candidate and MSS statistics. -/
lean_exe «sharing-study» where
  root := `Benchmarks.SharingStudy

/-- The binder-data sections of compiled environments: sizes, and two compiles compared. -/
lean_exe «binder-data-stats» where
  root := `Benchmarks.BinderDataStats

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
per-member pieces (`pieces/<Q>.ixe`, one `ix compile`
process each) and assembles + verifies the `truthmines.ixc` catalog
manifest. Needs `lake build ix` first for the `build` verb. -/
lean_exe truthmines where
  root := `Benchmarks.TruthMinesSpec.Main

/-- Typed manifest for the focused anonymous FLT regression suite
(`Benchmarks/Kernel/AnthropicFLT/Cases.lean`). -/
lean_lib AnthropicFLT where
  roots := #[`Benchmarks.Kernel.AnthropicFLT.Cases]

/-- Typed benchmark manifests and comparison records for formal Aiur
(`Benchmarks/FormalAiur/`). -/
lean_lib FormalAiurBenchmarks where
  globs := #[.submodules `Benchmarks.FormalAiur]

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
`IxCK/` (its own package, globbed, `lake -d IxCK build --wfail`) and
`IxSharingVerify/` (a globbed library, built by `lake lint`) are covered by
their own targets, and `IxVMRefinement/` (a globbed library) by the refinement
step only; `Models/` and every directory with its own lakefile are
other workspaces. The nested Aiur, IxVM and MultiStark packages are built
with `--wfail` by their own CI step (`aiur/Aiur` globs every module; every
MultiStark module is reachable from its library or executable root, and so is
every IxVM module but the derived semantic helpers `IxVM.Lookup`,
`IxVM.Mirrors.*` and `IxVM.Obs.*`, which the refinement step builds). -/
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

/-- Executable targets that import the nested formal/Mathlib packages and are
checked in the formal CI job (`check-formal-modules`) when `build-all` runs
with `--host-only`. -/
def formalOnlyExes : List String := ["formal-package-tests"]

/-- Modules under `coveredDirs` whose transitive imports reach Mathlib (through
`Aiur`/`IxVM`/`MultiStark`). `checkModules` splits them from `--host-only` so
host CI builds require no Mathlib cache, while `check-formal-modules` builds
this exact complement in the formal CI job. -/
def isFormalOnlyModule (m : Lean.Name) : Bool :=
  let s := m.toString
  (s.startsWith "Ix.IxVM.Refinement." && m != `Ix.IxVM.Refinement.Claim) ||
  (s.startsWith "Ix.IxVM.Consistency." &&
    m != `Ix.IxVM.Consistency.ReaderAdmission &&
    m != `Ix.IxVM.Consistency.ReaderFootprint) ||
  m == `Ix.IxVM.ConsistencyAudit ||
  s.startsWith "Ix.Cert.MultiStark." ||
  s.startsWith "Ix.Cert.MultiStarkRefinement." ||
  s.startsWith "Ix.Cert.Aggr." ||
  s.startsWith "Ix.Cert.Compression." ||
  s.startsWith "Ix.Cert.AiurCompression." ||
  m == `Ix.Cert.Security128ClosureManifest ||
  m == `Ix.Cert.StatementClosureManifest ||
  m == `Ix.Cert.AiurCompressionClosureManifest ||
  m == `Ix.Cert.RecordSectionsBridge ||
  m == `Tests.FormalPackageMain ||
  m == `Tests.Ix.MultiStarkVerifier ||
  m == `Tests.Ix.InstanceSymbols ||
  m == `Tests.Ix.VMSource ||
  m == `Tests.Ix.IxVM.SafeReferencesWalk ||
  m == `Tests.Ix.Kernel.ModelLaws

inductive ModuleScope where
  | all
  | hostOnly
  | formalOnly
  deriving BEq

/-- The module-coverage gate: check `moduleExclusions`, require every covered
module to be buildable (under a library root or an executable root), then
`lake build <args> +M…` every selected covered module that is not excluded. -/
def checkModules (args : List String) (scope : ModuleScope := .all) : ScriptM UInt32 := do
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
  let selected := match scope with
    | .all => built
    | .hostOnly => built.filter (!isFormalOnlyModule ·)
    | .formalOnly => built.filter isFormalOnlyModule
  let scopeLabel := match scope with
    | .all => "all"
    | .hostOnly => "host-only"
    | .formalOnly => "formal-only"
  IO.println s!"[check-modules] building {selected.size} ({scopeLabel}) of {built.size} modules under \
    {coveredDirs.toList} and the root files; {excluded.size} left out: {excluded.toList}"
  if selected.isEmpty then return 0
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["build"] ++ args.toArray ++ selected.map (s!"+{·}")
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

/-- Libraries `build-all` leaves to their own step (see each library's comment). -/
def separateLibs : List String := ["IxVMRefinement"]

@[lint_driver]
script "build-all" (args) := do
  let hostOnly := args.contains "--host-only"
  let buildArgs := args.filter (· != "--host-only")
  let pkg ← getRootPackage
  let libNames := pkg.configTargets LeanLib.configKind |>.map (·.name.toString)
    |>.filter (!separateLibs.contains ·)
  let exeNames := pkg.configTargets LeanExe.configKind |>.map (·.name.toString)
    |>.filter fun n => !hostOnly || !formalOnlyExes.contains n
  let allNames := libNames ++ exeNames
  let mut failed : Array String := #[]
  IO.println s!"Building {allNames.size} targets in one batched Lake build{if hostOnly then " (host-only)" else ""}"
  let batch ← IO.Process.spawn {
    cmd := "lake", args := #["build"] ++ buildArgs.toArray ++ allNames
    stdout := .inherit, stderr := .inherit }
  if (← batch.wait) != 0 then failed := failed.push "targets"
  IO.println "Building: every module under the covered directories (check-modules)"
  let scope := if hostOnly then .hostOnly else .all
  if (← checkModules buildArgs scope) != 0 then failed := failed.push "check-modules"
  IO.println "Checking: source terminology (check-source-docs)"
  let hygiene ← IO.Process.spawn {
    cmd := "lake", args := #["env", "lean", "--run", "Scripts/SourceHygiene.lean"]
    stdout := .inherit, stderr := .inherit }
  if (← hygiene.wait) != 0 then failed := failed.push "check-source-docs"
  IO.println "Checking: CI path-filter coverage of closure manifests (check-ci-filters)"
  let ciFilters ← IO.Process.spawn {
    cmd := "lake", args := #["env", "lean", "--run", "Scripts/CheckCiFilters.lean"]
    stdout := .inherit, stderr := .inherit }
  if (← ciFilters.wait) != 0 then failed := failed.push "check-ci-filters"
  if failed.isEmpty then return 0
  IO.eprintln s!"Failed {failed.size} build and lint check(s): {", ".intercalate failed.toList}"
  return 1

/-- Reject retired compiler APIs and private planning references in source
and documentation. The scanner has no grandfather baseline. -/
script "check-source-docs" := do
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["env", "lean", "--run", "Scripts/SourceHygiene.lean"]
    stdout := .inherit, stderr := .inherit }
  return ← child.wait

/-- Verify `.github/workflows/ci.yml` path filters cover every project module
in the transitive definitional closure manifests and TCB fence files. -/
script "check-ci-filters" := do
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["env", "lean", "--run", "Scripts/CheckCiFilters.lean"]
    stdout := .inherit, stderr := .inherit }
  return ← child.wait

/-- Verifying-key gate comparing `lake exe formal-keys` against `tools/formal-aiur.keys`.
Accepts `--check` (default), `--update`, `--self-test`, or `--help`. -/
script "check-formal-keys" (args) := do
  let child ← IO.Process.spawn {
    cmd := "lean", args := #["--run", "Scripts/CheckFormalKeys.lean"] ++ args.toArray
    stdout := .inherit, stderr := .inherit }
  return ← child.wait

/-- Build and verify (or with `--update`, regenerate) committed Aiur compression
compiler fixtures under `crates/aiur/tests/fixtures/`. -/
script "check-aiur-compression-fixtures" (args) := do
  let child ← IO.Process.spawn {
    cmd := "lean",
    args := #["--run", "Scripts/CheckAiurCompressionFixtures.lean"] ++ args.toArray
    stdout := .inherit, stderr := .inherit }
  return ← child.wait

/-- The module-coverage gate (`checkModules`), always strict. `lake lint`
runs it too, with the lint arguments. Accepts `--host-only`. -/
script "check-modules" (args) := do
  let hostOnly := args.contains "--host-only"
  let buildArgs := args.filter (· != "--host-only")
  return ← checkModules ("--wfail" :: buildArgs) (if hostOnly then .hostOnly else .all)

/-- Build the Mathlib-dependent root executables and covered modules that
`build-all --host-only` leaves to the formal CI job. -/
script "check-formal-modules" (args) := do
  let buildArgs := "--wfail" :: args
  let exes := formalOnlyExes.toArray
  unless exes.isEmpty do
    let child ← IO.Process.spawn {
      cmd := "lake", args := #["build"] ++ buildArgs.toArray ++ exes
      stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do return 1
  return ← checkModules buildArgs .formalOnly

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

section IxVMRefinement

/-- **The IxVM refinement proofs**: every module under `IxVMRefinement/`. They are
written against the path lemmas of the IxVM functions, which the modules `IxVM.Obs.*` of
the IxVM package derive from `IxVM.source` when they are elaborated
(`Aiur.Generic.Derive`): building this library builds those too, at the cost of checking
every derived proof. Built only by the refinement step,
`lake build --wfail IxVMRefinement`: it is not a default target, its directory is not
one of `coveredDirs`, and `build-all` (the lint driver) skips it (`separateLibs`). -/
lean_lib IxVMRefinement where
  globs := #[.submodules `IxVMRefinement]

end IxVMRefinement

section IxCK

/- The `ix-ck` dependency owns the certified modules and their artifacts.
`lake -d IxCK build --wfail` checks them without host dependencies;
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

/-- The role-table generator: regenerates `IxCK/Kernel/Ixon/RoleData.lean` (the
default role table, its evidence records and the Ixon prelude) from a compiled
Init (`.lake/envs/initstd.ixe`), each binding validated by the verified fold,
and Source mode's evidence from the certificate module's environment, which it
loads as `kernel-source-ingress` does (hence the interpreter). -/
lean_exe «kernel-pin-gen» where
  root := `Benchmarks.Kernel.PinGen
  supportInterpreter := true
  moreLinkObjs := #[ix_rs]

/-- Run `cmd args`, inheriting the output, and fail on a nonzero exit code. -/
def runChecked (cmd : String) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn { cmd, args, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do
    throw <| IO.userError s!"{cmd} {args} failed with exit code {code}"

/-- The certified kernel gate's roots for the full-closure kernel replay: its
audit and freeze modules (the modules CI's kernel job also names to
`leanchecker`) and the certified sharing library. The replay re-checks every
project module in their import closure, so a lemma below them that entered an
`.olean` without a kernel check fails the gate. -/
def kernelReplayRoots : Array String := #[
  "IxCK.Kernel.Audit.Roots", "IxCK.Kernel.Admission.Audit",
  "Ix.Ixon.Projection.Audit", "Ix.Ixon.BlockOrder.Audit", "Ix.Ixon.Authenticated.Audit",
  "Ix.HostAdmission.Audit", "Ix.Cert.RuntimeAudit", "Ix.Cert.ModuleAudit", "Ix.Cert.Audit",
  "Ix.Cert.ClosureManifest", "Ix.SpecDigest",
  "IxSharingVerify", "IxSharingVerify.Audit.Statements", "IxSharingVerify.Audit.CompiledCode",
  "IxSharingVerify.Audit.SorryFrontier",
  "IxCK.Kernel", "IxCK.Resource", "IxCK.Address.Core"]

/-- Every module of the certified kernel package (its libraries glob these
directories) and of the certified sharing library, replayed whether or not an
audit root imports it: the kernel theory only IxVM's consistency proof uses is
here too. -/
def kernelReplayTrees : Array String := #[
  "IxCK/Kernel:IxCK.Kernel", "IxCK/Ixon:IxCK.Ixon", "IxCK/Resource:IxCK.Resource",
  "IxCK/Fixtures:IxCK.Fixtures", "IxSharingVerify:IxSharingVerify"]

/-- Build the kernel replay's roots, then replay their closure (and, with the
model, the set-theory model's) with Lean's kernel (`Scripts/KernelReplay.lean`). -/
def kernelReplay (withModel : Bool) : IO Unit := do
  runChecked "lake" #["-d", "IxCK", "build", "--wfail"]
  runChecked "lake" (#["build", "--wfail"] ++ kernelReplayRoots)
  runChecked "lake" (#["env", "lean", "--run", "Scripts/KernelReplay.lean", "--jobs", "8"] ++
    (kernelReplayTrees.flatMap fun t => #["--tree", t]) ++ kernelReplayRoots)
  if withModel then
    runChecked "lake" #["-d", "Models/SetTheory", "build", "--wfail"]
    runChecked "lake" #["-d", "Models/SetTheory", "env", "lean", "--run",
      "Scripts/KernelReplay.lean", "--jobs", "4",
      "--tree", "Models/SetTheory/IxSetTheoryModel:IxSetTheoryModel",
      "IxSetTheoryModel", "IxSetTheoryModel.Audit"]

/-- The certified kernel gate's full-closure kernel replay alone (`check-kernel`
runs it last). CI runs it on pushes to `main`, where the other checks are not
repeated. Accepts `--with-model`. -/
script "check-kernel-replay" (args) := do
  unless args.isEmpty || args == ["--with-model"] do
    IO.eprintln "usage: lake run check-kernel-replay [--with-model]"
    return 2
  kernelReplay (args == ["--with-model"])
  IO.println "Certified kernel replay passed."
  return 0

/-- Run the certified kernel gate: the standalone strict build with its audits,
the host-side tests, optionally the set-theory model, the certification
statements' freeze (`Ix.Cert.Audit`), the layering and
trust-surface fences, the certified entry's host-compiled
cases, the `.meta` and `.source` names against Lean's, and the full-closure
kernel replay of the kernel package and its audit roots (`check-kernel-replay`). -/
script "check-kernel" (args) := do
  unless args.isEmpty || args == ["--with-model"] do
    IO.eprintln "usage: lake run check-kernel [--with-model]"
    return 2
  let run (cmd : String) (args : Array String) : ScriptM Unit := runChecked cmd args
  run "lake" #["-d", "IxCK", "build", "--wfail"]
  -- Batch all root-workspace kernel audit modules, freeze, fences and host-entry
  -- executables into one Lake invocation so dependency tracing runs once.
  run "lake" #["build", "--wfail",
    "Ix.Ixon.Projection.Audit", "Ix.Ixon.BlockOrder.Audit", "Ix.Ixon.Authenticated.Audit",
    "Ix.HostAdmission.Audit",
    "Ix.Cert.RuntimeAudit", "Ix.Cert.ModuleAudit", "Ix.Cert.Audit", "Ix.Cert.ClosureManifest",
    "Tests.Ix.Kernel.BlockOrder", "Tests.Ix.Kernel.AddressPure", "Tests.Ix.Kernel.Projection",
    "Tests.Ix.Kernel.Reader", "Tests.Ix.Kernel.CertifiedEntry", "Tests.Ix.Kernel.Authentication",
    "Tests.Ix.Kernel.Contracts", "Tests.Ix.Kernel.ModelLaws", "Tests.Ix.Kernel.Axioms",
    "Ix.SpecDigest", "Tests.Ix.Kernel.Erasure",
    "kernel-layering", "kernel-trust-surface", "kernel-entry-cases", "kernel-meta-names"]
  if args == ["--with-model"] then
    run "lake" #["-d", "Models/SetTheory", "build", "--wfail"]
  -- The kernel's fences, derived from con-leche's: import layering and the
  -- per-file escape allowlist, with the trust-surface lexer's self-test.
  run ".lake/build/bin/kernel-layering" #[]
  run ".lake/build/bin/kernel-trust-surface" #[]
  -- Host-compiled Lean declarations through the certified entry, each with
  -- an exact expected verdict (`Tests/Ix/Kernel/EntryCases.lean`).
  let entry ← IO.Process.output { cmd := ".lake/build/bin/kernel-entry-cases" }
  IO.FS.writeFile ".lake/build/kernel-entry-cases.jsonl" entry.stdout
  IO.eprint entry.stderr
  unless entry.exitCode == 0 do
    IO.eprint entry.stdout
    throw <| IO.userError "kernel-entry-cases failed; see .lake/build/kernel-entry-cases.jsonl"
  -- The `.meta` and `.source` names against Lean's, on ill-typed declarations
  -- and the fixtures (`Tests/Ix/Kernel/MetaNames.lean`).
  run ".lake/build/bin/kernel-meta-names" #[]
  -- Every project module below the audit roots, and every module of the
  -- kernel package, re-checked by Lean's kernel.
  kernelReplay (args == ["--with-model"])
  IO.println "Certified kernel checks passed."
  return 0

/-- The theorems `Models/KernelBridge/IxKernelBridge/Audit.lean` fences with
`#guard_msgs in #print axioms`. `check-kernel-bridge` fails unless the fenced
set is exactly this list, so removing or adding a fence also changes this
inventory. -/
def kernelBridgeFences : List String := [
  "IxKernelBridge.srcRun_to_red",
  "IxKernelBridge.red_to_denotes_nat",
  "IxKernelBridge.infer_red_to_denotes_nat",
  "IxKernelBridge.srcRun_to_denotes_nat",
  "IxKernelBridge.srcRun_infer_to_denotes_nat",
  "IxKernelBridge.checkDecls_srcRun_denotes_nat",
  "IxKernelBridge.checkDecls_recheck_x86_denotes_nat",
  "IxKernelBridge.checkDecls_verifyBytes_immortal_denotes_nat",
  "IxKernelBridge.Examples.add_premise",
  "IxKernelBridge.Examples.sub_premise",
  "IxKernelBridge.Examples.mul_premise",
  "IxKernelBridge.Examples.div_premise",
  "IxKernelBridge.Examples.mod_premise",
  "IxKernelBridge.Examples.gcd_premise",
  "IxKernelBridge.Examples.land_premise",
  "IxKernelBridge.Examples.lor_premise",
  "IxKernelBridge.Examples.xor_premise",
  "IxKernelBridge.Examples.shiftLeft_premise",
  "IxKernelBridge.Examples.shiftRight_premise",
  "IxKernelBridge.Examples.beq_premise_false",
  "IxKernelBridge.Examples.ble_premise_false",
  "IxKernelBridge.Examples.pow_premise_false",
  "IxKernelBridge.Examples.id_bridge",
  "IxKernelBridge.Examples.succ_bridge",
  "IxKernelBridge.Examples.add_bridge",
  "IxKernelBridge.Examples.addLit_bridge",
  "IxKernelBridge.Examples.addLit_concrete",
  "IxKernelBridge.KernelFront.infer_derives",
  "IxKernelBridge.KernelFront.whnf_derives",
  "IxKernelBridge.KernelFront.annotate_runs",
  "IxKernelBridge.KernelFront.classifyTerm_derivations",
  "IxKernelBridge.KernelFront.classifyTerm_sound"]

/-- Build the kernel-bridge model (`Models/KernelBridge`, a workspace of its
own that requires `IxCK` and `IxCC` by path: a conditional simulation lemma
between IxCC's source evaluator and the kernel's reduction; its README states
the scope), whose modules treat warnings as errors and whose audit module
holds the axiom fences, then check that the fenced theorems are exactly
`kernelBridgeFences` and that no `#print axioms` is unguarded. Run from the
repository root. The merge-queue kernel partition runs it beside
`check-kernel --with-model`. -/
script "check-kernel-bridge" (args) := do
  unless args.isEmpty do
    IO.eprintln "usage: lake run check-kernel-bridge"
    return 2
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["-d", "Models/KernelBridge", "build"],
    stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do
    IO.eprintln s!"lake -d Models/KernelBridge build failed with exit code {code}"
    return 1
  let marker := "#guard_msgs in #print axioms "
  let lines := (← IO.FS.readFile "Models/KernelBridge/IxKernelBridge/Audit.lean").splitOn "\n"
  let fenced := lines.filterMap fun line =>
    if line.startsWith marker then some (line.drop marker.length).toString.trimAscii.toString
    else none
  let unguarded := lines.filter fun line =>
    line.trimAscii.toString.startsWith "#print axioms"
  let missing := kernelBridgeFences.filter (!fenced.contains ·)
  let extra := fenced.filter (!kernelBridgeFences.contains ·)
  unless unguarded.isEmpty && missing.isEmpty && extra.isEmpty &&
      fenced.eraseDups.length == fenced.length do
    IO.eprintln s!"kernel-bridge fence inventory changed: missing {missing}, unlisted {extra}, unguarded {unguarded}, {fenced.length - fenced.eraseDups.length} duplicates"
    return 1
  IO.println s!"Kernel bridge checks passed: {fenced.length} exact axiom fences."
  return 0

end IxCK
