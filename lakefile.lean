import Lake
open System Lake DSL

package ix where
  version := v!"0.1.0"

lean_lib Ix

@[default_target]
lean_exe ix where
  root := `Main
  extraDepTargets := #[`ffi, `ix_rust]
  moreLinkArgs := #[
      "-Wl,--start-group",
      FilePath.toString (".lake" / "build" / "lib" / nameToStaticLib "ffi"),
      FilePath.toString ("target" / "release" / nameToStaticLib "ix"),
      "-Wl,--end-group"
    ]

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "ca8e2803f89f0c12bf9743ae7abbfb2ea6b0eeec"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "efa5aa20504b88e2826032ddaa606c7965ec9467"

section Tests

lean_exe Tests.Blake3
lean_exe Tests.ByteArray

end Tests

section FFI

/- Build `ffi.o` -/
target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile "ffi.c"
  let includeDir ← getLeanIncludeDir
  let weakArgs := #["-I", includeDir.toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace


/- Build the static lib from `ffi.o` -/
target ffi pkg : FilePath := do
  let name := nameToStaticLib "ffi"
  let ffiO ← ffi.o.fetch
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

/- Build the static lib for the Rust crate -/
target ix_rust pkg : FilePath := do
  proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir }
  let name := nameToStaticLib "ix"
  let srcPath := pkg.dir / "target" / "release" / name
  return pure srcPath

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
