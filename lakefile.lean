import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

@[default_target]
lean_lib Ix

lean_exe ix where
  root := `Main
  supportInterpreter := true

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "1fc461a9b83eeb68da34df72cec2ef1994e906cb"

require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "a5ed3f0bceda9506271a8f95c365e9bd0040288d"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "41c5d0b8814dec559e2e1441171db434fe2281cc"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "d117e2c28cba42e974bc22568ac999492a34e812"

section Tests

lean_lib Tests

@[test_driver]
lean_exe Tests.Main where
  supportInterpreter := true

end Tests

lean_lib IxTest where
  srcDir := "ix_test"

section IxApplications

section Benchmarks

lean_exe «bench-aiur» where
  root := `Benchmarks.Aiur

lean_exe «bench-blake3» where
  root := `Benchmarks.Blake3

end Benchmarks

lean_lib Apps

lean_exe Apps.ZKVoting.Prover where
  supportInterpreter := true
lean_exe Apps.ZKVoting.Verifier

end IxApplications

section FFI

/-- Build the static lib for the C files -/
extern_lib ix_c pkg := do
  let compiler := "gcc"
  let cDir := pkg.dir / "c"
  let buildCDir := pkg.buildDir / "c"
  let weakArgs := #["-fPIC", "-I", (← getLeanIncludeDir).toString, "-I", cDir.toString]

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
  buildStaticLib (pkg.staticLibDir / libName) buildJobs

/-- Build the static lib for the Rust crate -/
extern_lib ix_rs pkg := do
  -- Default to `--features parallel`, configured via env var
  let ixNoPar ← IO.getEnv "IX_NO_PAR"
  let ixNet ← IO.getEnv "IX_NET"
  let buildArgs := #["build", "--release"]
  let args := match (ixNoPar, ixNet) with
  | (some "1", some "1") => buildArgs ++ ["--features", "net"]
  | (some "1", _) => buildArgs
  | (_, some "1") => buildArgs ++ ["--features", "parallel,net"]
  | _ => buildArgs ++ ["--features", "parallel"]
  proc { cmd := "cargo", args, cwd := pkg.dir } (quiet := true)
  let libName := nameToStaticLib "ix_rs"
  inputBinFile $ pkg.dir / "target" / "release" / libName

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
  let cachedLeanHHash := 1323938820889983873

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
