import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

@[default_target]
lean_lib Ix

lean_exe ix where
  root := `Main

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "8ff598482515a698c88f2e65f7f529a04cf636f1"

require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "29018d578b043f6638907f3425af839eec345361"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "e7fd1a415c80985ade02a021172834ca2139b0ca"

section Tests

lean_lib Tests

@[test_driver]
lean_exe Tests.Main

end Tests

section IxApplications

lean_lib Apps

lean_exe Apps.ZKVoting.Prover
lean_exe Apps.ZKVoting.Verifier

end IxApplications

section FFI

/-- Build the static lib for the Rust crate -/
extern_lib ix_rs pkg := do
  proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir } (quiet := true)
  let libName := nameToStaticLib "ix_rs"
  let libPath := pkg.dir / "target" / "release" / libName

  -- If the static lib has changed, remove cached binaries for recompilation
  let libBytes ← IO.FS.readBinFile libPath
  let libHash := toString $ hash libBytes
  let libHashPath := pkg.nativeLibDir / libName |>.addExtension "hash"
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

/-- Build the static lib for the C files -/
extern_lib ix_c pkg := do
  let compiler := "cc"
  let cDir := pkg.dir / "c"
  let buildCDir := pkg.buildDir / "c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", cDir.toString]

  let cDirEntries ← cDir.readDir

  -- Include every C header file in the trace mix
  let extraDepTrace := cDirEntries.foldl (init := getLeanTrace) fun acc dirEntry =>
    let filePath := dirEntry.path
    if filePath.extension == some "h" then do
      let x ← acc
      let y ← computeTrace $ TextFilePath.mk filePath
      pure $ x.mix y
    else acc

  -- Collect a build job for every C file in `cDir`
  let mut buildJobs := #[]
  for dirEntry in cDirEntries do
    let filePath := dirEntry.path
    if filePath.extension == some "c" then
      let oFile := buildCDir / dirEntry.fileName |>.withExtension "o"
      let srcJob ← inputTextFile filePath
      let buildJob ← buildO oFile srcJob weakArgs #[] compiler extraDepTrace
      buildJobs := buildJobs.push buildJob

  let libName := nameToStaticLib "ix_c"
  buildStaticLib (pkg.nativeLibDir / libName) buildJobs

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

script "check-lean-h-hash" := do
  let cachedLeanHHash := 2268578318159647227

  let leanIncludeDir ← getLeanIncludeDir
  let includedLeanHPath := leanIncludeDir / "lean" / "lean.h"
  let includedLeanHBytes ← IO.FS.readBinFile includedLeanHPath
  let includedLeanHHash := includedLeanHBytes.hash

  if cachedLeanHHash ≠ includedLeanHHash then
    IO.eprintln   "Mismatching lean/lean.h hash"
    IO.eprintln   "  1. Double-check changes made to lean/lean.h"
    IO.eprintln s!"  2. Cache {includedLeanHHash} instead"
    return 1
  return 0

end Scripts
