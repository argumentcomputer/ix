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
  "https://github.com/argumentcomputer/LSpec" @ "7f5bb9de3aab89c2c24a1c917b17d9b75e6f220e"

require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @ "686c397ae8a540b25bf6b18bbd4fb9f6cf0459e8"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.27.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.27.0"

section Tests

lean_lib Tests

@[test_driver]
lean_exe IxTests where
  root := `Tests.Main
  supportInterpreter := true

end Tests

section Benchmarks

lean_exe «bench-aiur» where
  root := `Benchmarks.Aiur

lean_exe «bench-blake3» where
  root := `Benchmarks.Blake3

lean_exe «bench-sha256» where
  root := `Benchmarks.Sha256

lean_exe «bench-shardmap» where
  root := `Benchmarks.ShardMap

end Benchmarks

section IxApplications

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
  -- Defaults to `--features parallel`, configured via env var
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

script "check-lean-h-hash" := do
  let cachedLeanHHash := 11953097959587138033

  let leanIncludeDir ← getLeanIncludeDir
  let includedLeanHPath := leanIncludeDir / "lean" / "lean.h"
  let includedLeanHBytes ← IO.FS.readBinFile includedLeanHPath
  let includedLeanHHash := includedLeanHBytes.hash

  if cachedLeanHHash ≠ includedLeanHHash then
    IO.eprintln   "Mismatching lean/lean.h hash"
    IO.eprintln   "  1. Double-check changes made to lean/lean.h"
    IO.eprintln s!"  2. Cache {includedLeanHHash} instead"
    return 1
  else
    IO.println "lean/lean.h hash matches ✓"
  return 0

script "get-exe-targets" := do
  let pkg ← getRootPackage
  let exeTargets := pkg.configTargets LeanExe.configKind
  for tgt in exeTargets do
    IO.println <| tgt.name.toString |>.dropPrefix "«" |>.dropSuffix "»" |>.toString
  return 0

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
