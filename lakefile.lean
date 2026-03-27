import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "928f27c7de8318455ba0be7461dbdf7096f4075a"

require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "40dc7036b09531cf084f3554a8873eaa4d92a9bc"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.28.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.28.0"

/-! ## FFI

The Rust static lib uses `target` + `moreLinkObjs` instead of `extern_lib` because
`lake test` needs the `test-ffi` Cargo feature for Rust test-only code,
but `lake build` should not include it. The `ix_rs` and `ix_rs_test` targets both write
to the same lib path; `ix_rs_test` calls `ix_rs.fetch` to ensure `ix_rs` completes first,
then overwrites the lib with test-ffi symbols. An `extern_lib` would always run last
(at link time) and overwrite the test-ffi build.

Note: `extern_lib` only runs at link time, so `lake build` on a `lean_lib` alone wouldn't
trigger the Cargo build. With `target` + `moreLinkObjs`, the Rust static lib is built during
module compilation on the default `Ix` lib.
-/
section FFI

/-- Build args for `cargo build --release` with feature flags from env vars.
Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) : IO (Array String) := do
  -- IX_NO_PAR=1 disables parallel; IX_NET=1 enables networking (iroh)
  let ixNoPar ← IO.getEnv "IX_NO_PAR"
  let ixNet ← IO.getEnv "IX_NET"
  let mut features : Array String := #[]
  if ixNoPar != some "1" then features := features.push "parallel"
  if ixNet == some "1" then features := features.push "net"
  if testFfi then features := features.push "test-ffi"
  let buildArgs := #["build", "--release"]
  if features.isEmpty then return buildArgs
  else return buildArgs ++ #["--features", ",".intercalate features.toList]

/-- Build the Rust static lib without `test-ffi` (default for `lake build`). -/
target ix_rs pkg : FilePath := do
  let args ← cargoArgs
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToStaticLib "ix_rs"

/-- Rebuild the Rust static lib with `test-ffi`.
Only triggered by `lake test` (via `moreLinkObjs` on `IxTests`).
Fetches `ix_rs` first to guarantee ordering before overwriting the lib. -/
target ix_rs_test pkg : FilePath := do
  let _ ← ix_rs.fetch
  let args ← cargoArgs (testFfi := true)
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToStaticLib "ix_rs"

end FFI

@[default_target]
lean_lib Ix where
  moreLinkObjs := #[ix_rs]
  precompileModules := true

lean_exe ix where
  root := `Main
  supportInterpreter := true

section Tests

lean_lib Tests

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true
  moreLinkObjs := #[ix_rs_test]

lean_exe kernel where
  root := `Kernel
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

lean_exe «bench-check-nat-add-comm» where
  root := `Benchmarks.CheckNatAddComm
  supportInterpreter := true

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
  let allNames := libNames ++ exeNames |>.toList
  for name in allNames do
    IO.println s!"Building: {name}"
    let child ← IO.Process.spawn {
      cmd := "lake", args := #["build", name] ++ args
      stdout := .inherit, stderr := .inherit }
    let exitCode ← child.wait
    if exitCode != 0 then return exitCode
  return 0

end Scripts
