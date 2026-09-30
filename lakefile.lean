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

/- The compiler (M1.I1): `compilatrix compile CLOSURE.ixe --equations EQ.json
--root NAME -o OUT.o` runs ingress, `produce` and `Recheck.run` and writes the
ELF object; `compilatrix check-cert` rechecks a certificate. The logic is in
`Compilatrix.Cli`; the root only calls it. -/
lean_exe compilatrix where
  root := `Compilatrix.Cli.Main

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

/- Lam and erasure (design note 02 §4–5, §13): Lam's rules, erasure on
synthetic programs, SrcEval against Lam on K1, bench-k1 and src-sortpoly
(readback, traps, least clocks), the native differential, annotation
mutation, well-formedness and static modes of every erased program. -/
lean_exe «tests-lam» where
  root := `CompilatrixTests.Lam.Main

/- Regenerates (or with `--check` compares) the K1 artifacts the kernel
evaluates: `CompilatrixTests/Src/Artifacts/*.lean`, the loaded fib, tak and
gcd programs with their annotations as Lean terms (M1.K1). -/
lean_exe «gen-src-artifacts» where
  root := `CompilatrixTests.Src.ArtifactMain

/- Anf and the middle-end passes P1–P4 (design note 02 §6–8, §13): Lam
against Anf after every pass on k1.ixe and bench-k1, the K1 shape
expectations, generated Lam programs under random oracles, WellScoped and
shrink idempotence, and the passes re-run by the kernel. -/
lean_exe «tests-anf» where
  root := `CompilatrixTests.Anf.Main

/- Fir, the Phase 1 Own fragment and Cfg (design note 03, M1.F5): every
root and first-order constant of k1.ixe and bench-k1 through Anf → Fir →
Own → Cfg against Anf and Lam (readback, traps, each level's clock map and
timeout clause), the fallback route declined at Fir, generated first-order
programs, the bench entries at test sizes, well-formedness at every level,
and the lowerings re-run by the kernel. -/
lean_exe «tests-fir» where
  root := `CompilatrixTests.Fir.Main

/- The runtime lowering (design note 04, M1.F6): `Rt.lower` from Cfg to
Lir on k1.ixe, bench-k1 and generated programs against Cfg (related values,
typed readback, traps, the clock relation, heap and natOverflow), the
primitive sequences at their boundaries, `cx_init`, hand-written cases and
planted mutations; with `--cc`, `Backend.compile` to native objects run at
every level and under `fixtures/x86/runtime_driver.c`; and the lowering
re-run by the kernel. -/
lean_exe «tests-rt» where
  root := `CompilatrixTests.Rt.Main

/- The compiler end to end (M1.I1, M1.I2): the `compilatrix` command line on
the bench-k1 closures and k1.ixe (with `--cc`, linked with the runtime driver
and run at test and bench sizes), `produce` + `Recheck.run` against the stage
suites' pipeline, the certificate's JSON round trip, declines, and
certificate mutations (rejected, or code that agrees on every tested input). -/
lean_exe «tests-pipeline» where
  root := `CompilatrixTests.Pipeline.Main

/- Regenerates (or with `--check` compares) the recheck artifacts the kernel
evaluates (M1.K1): `CompilatrixTests/Recheck/Artifacts/*.lean`, each bench-k1
closure's `Src.Program`, configuration and certificate as shared Lean terms,
with the typed program and object bytes of the native run. -/
lean_exe «gen-recheck-artifacts» where
  root := `CompilatrixTests.Recheck.ArtifactMain

/- The recheck path in kernel-evaluable style (M1.K1): building it evaluates
`Recheck.runTyped` on the fib, tak and gcd artifacts by `decide +kernel`;
running it checks every committed artifact against a fresh ingress,
`produce` and native run. -/
lean_exe «tests-recheck» where
  root := `CompilatrixTests.Recheck.Main

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

/- Stacking, layout and emission: hand-written Xl, the Lir kernels and
generated Lir to ELF objects, run on the typed machine, the byte machine
and (with `--cc`) natively under `fixtures/x86/backend_driver.c`. -/
lean_exe «check-backend» where
  root := `CompilatrixTests.Backend.Main

/- MEAS-4 (M1.B6): the Lir kernels fib, sumLoop and gcd as ELF objects, with
their static spill and move counts and compile times, for the optional
measurement in benchmarks/meas4 (not a CI gate). -/
lean_exe «backend-probe» where
  root := `CompilatrixTests.Backend.ProbeMain

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
