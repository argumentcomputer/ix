import Lake

open System Lake DSL

package compilatrix where
  /- CI distributes many executables together. Resolve Lean/Lake symbols from
  the pinned shared libraries before the default static archives, avoiding a
  separate copy of the compiler runtime in every test binary. -/
  moreLinkArgs := match get_config? ciLeanLibDir with
    | some directory => #[s!"-Wl,-rpath,{directory}", "-lLake_shared", "-lleanshared",
        "-lleanshared_2", "-lleanshared_1", "-lInit_shared"]
    | none => #[]

/- Pure Aiur target definitions and abstract counter/order lemmas. -/
lean_lib AiurReference where
  srcDir := "vendor/aiur"
  roots := #[`Ix.Aiur, `Ix.IndexMap, `Ix.Lib]

/- Blake3 FFI. Keep this revision in lockstep with the flake's
`blake3-lean` input and `lake-manifest.json`. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @
  "c32002eeed36c520dfb73de32ef53483652e3aa5"

@[default_target]
lean_lib Compilatrix where
  roots := #[`Compilatrix]

/- Test modules are separate from the production import root. -/
lean_lib CompilatrixTests where
  roots := #[`CompilatrixTests]

lean_exe «tests-ixon-v3» where
  root := `CompilatrixTests.IxonV3.Main
  needs := #[.mk (.packageTarget .anonymous `«check-ixon-v3-catalog»)]

lean_exe «check-ixon-v3» where
  root := `CheckIxonV3

lean_exe «check-ixon-v3-catalog» where
  root := `CheckIxonV3Catalog

lean_exe «tests-aiur» where
  root := `CompilatrixTests.Aiur.Main

lean_exe «check-aiur» where
  srcDir := "scripts"
  root := `CheckAiur

/- Emit deterministic ELF fixtures for the independent object/link gate. -/
lean_exe «x86-object-fixture» where
  root := `X86ObjectFixture

lean_exe «check-x86-encoder» where
  srcDir := "scripts"
  root := `CheckX86Encoder

lean_exe «check-x86-bytes» where
  srcDir := "scripts"
  root := `CheckX86Bytes

lean_exe «check-x86-streams» where
  srcDir := "scripts"
  root := `CheckX86Streams

lean_exe «check-x86-object» where
  srcDir := "scripts"
  root := `CheckX86Object

lean_exe «check-trusted-externs» where
  srcDir := "scripts"
  root := `CheckTrustedExterns

lean_exe «check-tools-tests» where
  srcDir := "scripts"
  root := `CheckToolsTests

lean_exe «check-build-graph» where
  srcDir := "scripts"
  root := `CheckBuildGraph
