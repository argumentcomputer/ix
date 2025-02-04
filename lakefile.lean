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

section Tests

lean_exe Tests.Blake3
lean_exe Tests.ByteArray

end Tests

section FFI

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile "ffi.c"
  let includeDir ← getLeanIncludeDir
  let weakArgs := #["-I", includeDir.toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib liblean_ffi pkg := do
  let name := nameToStaticLib "ffi"
  let ffiO ← ffi.o.fetch
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

extern_lib rust_ffi pkg := do
  proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir }
  let name := nameToStaticLib "ix"
  let srcPath := pkg.dir / "target" / "release" / name
  return pure srcPath

end FFI
