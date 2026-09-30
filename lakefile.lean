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

/- The K1 research fixture compiled natively: the independent oracle of the
Src differential suite. Test-only; nothing in `Compilatrix` imports it. -/
lean_lib K1Fixture where
  srcDir := "fixtures/ixon-v3/k1"
  roots := #[`K1]

/- The sort-polymorphism fixture compiled natively: the independent oracle of
the level-exact relevance regression (D18). Test-only, like `K1Fixture`. -/
lean_lib SortPolyFixture where
  srcDir := "fixtures/ixon-v3/src-sortpoly"
  roots := #[`SortPoly]

/- Src: rules, the K1 table and runs, the native differential, pins,
diagnostics and the bench-k1 entries (design note 01 §10). -/
lean_exe «tests-src» where
  root := `CompilatrixTests.Src.Main

/- Src rows over the 60 s budget: `ack 3 10`, `fib 30` without primitives. -/
lean_exe «tests-src-slow» where
  root := `CompilatrixTests.Src.SlowMain

/- The relevance annotator and checker (design note 02 §3, §13). -/
lean_exe «tests-relevance» where
  root := `CompilatrixTests.Src.Relevance.Main

lean_exe «tests-ixon-v3» where
  root := `CompilatrixTests.IxonV3.Main
  needs := #[.mk (.packageTarget .anonymous `«check-ixon-v3-catalog»)]

lean_exe «check-ixon-v3» where
  root := `CheckIxonV3

lean_exe «check-ixon-v3-catalog» where
  root := `CheckIxonV3Catalog

lean_exe «tests-aiur» where
  root := `CompilatrixTests.Aiur.Main

/- Lir: kernels, then generated SSA programs checked for well-formedness,
critical-edge splitting, clock monotonicity and exactness, and determinism. -/
lean_exe «check-lir» where
  root := `CompilatrixTests.Lir.Main

/- Selection: Lir.eval against Xv.eval on the kernels and on generated Lir, in
lock-step (outcome, memory and clock), with per-rule firing counts. -/
lean_exe «check-xv-select» where
  root := `CompilatrixTests.Xv.Main

/- Allocation (TT-3): linear scan, the validator and the all-slots fallback on
the kernels and on generated programs, with chaos seeds, validator mutation
and Xv.eval against Xl.eval on every accepted allocation. -/
lean_exe «check-regalloc» where
  root := `CompilatrixTests.Xv.Alloc.Main

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

/- Admission census over an Ixon v3 closure: first rejecting stage per constant. -/
lean_exe census where
  srcDir := "scripts"
  root := `Census

/- Differential check of the local x86 byte model against the host processor. -/
lean_exe «check-x86-hardware» where
  srcDir := "scripts"
  root := `CheckX86Hardware

/- Manual generator for `fixtures/ixon-v3/src-tables.tsv` (runs ix). -/
lean_exe «pin-src-tables» where
  srcDir := "scripts"
  root := `PinSrcTables
  supportInterpreter := true
