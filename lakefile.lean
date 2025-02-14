import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

lean_lib Ix

@[default_target]
lean_exe ix where
  root := `Main

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "ca8e2803f89f0c12bf9743ae7abbfb2ea6b0eeec"

require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "3eed804578f8b8a8cab122971d5b3bf04e729307"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "efa5aa20504b88e2826032ddaa606c7965ec9467"

section Tests

lean_exe Tests.Blake3
lean_exe Tests.ByteArray
lean_exe Tests.Rust

end Tests

section IxApplications

lean_lib Apps

lean_exe Apps.ZKVoting.Prover
lean_exe Apps.ZKVoting.Verifier

end IxApplications

section FFI

/-- Build the static lib for the Rust crate -/
extern_lib ix_rs pkg := do
  proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir }
  let libName := nameToStaticLib "ix_rs"
  let libPath := pkg.dir / "target" / "release" / libName

  -- If the static lib has changed, remove cached binaries for recompilation
  let libBytes ← IO.FS.readBinFile libPath
  let libHash := toString $ hash libBytes
  let libHashPath := pkg.nativeLibDir / (libName ++ ".hash")
  let shouldCleanBinaries ←
    if ← pkg.binDir.pathExists then
      if ← libHashPath.pathExists then
        let cachedHash ← IO.FS.readFile libHashPath
        pure $ libHash != cachedHash -- Clean up in case of hash mismatch
      else pure true -- No hash file
    else pure false -- No files to remove
  if shouldCleanBinaries then IO.FS.removeDirAll pkg.binDir
  IO.FS.writeFile libHashPath libHash

  return pure libPath

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
      let input := (← (← getStdin).getLine).trim
      pure $ if input.isEmpty then binDir else ⟨input⟩
    | none =>
      print s!"Target directory for the ix binary? "
      let input := (← (← getStdin).getLine).trim
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

end Scripts
