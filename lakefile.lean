import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"
  moreLinkArgs := #["target/release/" ++ nameToStaticLib "ix_rs"]

@[default_target]
lean_lib Ix where
  needs := #[`@/ix_rs]

lean_exe ix where
  root := `Main
  supportInterpreter := true

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "928f27c7de8318455ba0be7461dbdf7096f4075a"

require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "f89c732c481f87a47465041c6d7d659e1812848b"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.28.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.28.0"

section Tests

lean_lib Tests

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true
  needs := #[`@/ix_rs_test]

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

/-! ## FFI

We use `target` rather than `extern_lib` for the Rust static lib for two reasons:

1. **Build-time Rust compilation** `extern_lib` runs at link time (when an exe is linked),
   so `lake build` on a `lean_lib` alone would not trigger it. `target` runs during 
   module compilation (via `needs`), so `lake build` on the default `Ix` lib is enough
   to build the Rust crate.

2. **Test-ffi toggle** `lake test` needs the `test-ffi` Cargo feature; `lake build` does not.
   Two targets (`ix_rs` and `ix_rs_test`) write to the same lib path. `ix_rs_test` calls
   `ix_rs.fetch` to guarantee ordering, then overwrites the lib with test-ffi symbols.
   `extern_lib` would run last (at link time) and overwrite the test-ffi build instead.

`moreLinkArgs` is then needed on the `package` to tells the linker where to find the lib,
replacing the auto-linking that `extern_lib` provides.
-/
section FFI

/-- Build args for `cargo build --release` with feature flags from env vars.
    Feature flags:
      IX_NO_PAR=1  — disable parallel feature
      IX_NET=1     — enable networking (iroh)
    Cargo output is visible with `lake -v build`. -/
def cargoArgs (testFfi : Bool := false) : IO (Array String) := do
  let ixNoPar ← IO.getEnv "IX_NO_PAR"
  let ixNet ← IO.getEnv "IX_NET"
  let mut features : Array String := #[]
  if ixNoPar != some "1" then features := features.push "parallel"
  if ixNet == some "1" then features := features.push "net"
  if testFfi then features := features.push "test-ffi"
  let buildArgs := #["build", "--release"]
  if features.isEmpty then return buildArgs
  else return buildArgs ++ #["--features", ",".intercalate features.toList]

/-- Build the Rust static lib WITHOUT the `test-ffi` feature (default for `lake build`). -/
target ix_rs pkg : FilePath := do
  let args ← cargoArgs
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToStaticLib "ix_rs"

/-- Rebuild the Rust static lib WITH the `test-ffi` feature.
    Only triggered by `lake test` (via `needs` on `Tests`).
    Fetches `ix_rs` first to guarantee it completes before we overwrite
    the same lib file with the test-ffi version. -/
target ix_rs_test pkg : FilePath := do
  let _ ← ix_rs.fetch
  let args ← cargoArgs (testFfi := true)
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  inputBinFile $ pkg.dir / "target" / "release" / nameToStaticLib "ix_rs"

end FFI

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
