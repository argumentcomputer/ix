import Lake

open System Lake DSL

package «ix-cc» where
  /- CI distributes many executables together. Resolve Lean/Lake symbols from
  the pinned shared libraries before the default static archives, avoiding a
  separate copy of the compiler runtime in every test binary. -/
  moreLinkArgs := match get_config? ciLeanLibDir with
    | some directory => #[s!"-Wl,-rpath,{directory}", "-lLake_shared", "-lleanshared",
        "-lleanshared_2", "-lleanshared_1", "-lInit_shared"]
    | none => #[]

/- Blake3 FFI. Keep this revision in lockstep with ix's (`../lakefile.lean`),
the repository flake's `blake3-lean` input and `lake-manifest.json`. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @
  "3f8b805614a0bae1c033469ff893a8f0ee85f601"

/- Ix's certified-kernel package (`IxCK/`, no dependencies, no Rust).
Only its pure Ixon v4 codec (`IxCK.Ixon.Canonical` and its import closure, 11
modules) and the kernel's role vocabulary (`IxCK.Kernel.Key` and
`IxCK.Kernel.Name`) are imported: the codec by the ingress wire layer
(`IxCC.Ixon.V4.Convert`, `IxCC.Ixon.V3.Wire`) and the resource profile reader
(`IxCC.Src.Resource.Profile`), the roles by the reader of a role-bound
environment's binding (`IxCC.Ixon.V3.Binding`). It is the package beside this one in the ix
workspace; the trust ledger records the SHA-256 of every file of that
closure, so a change to it is reviewed here. -/
require «ix-ck» from "../IxCK"

@[default_target]
lean_lib IxCC where
  roots := #[`IxCC]

/- The compiler: `ixcc compile CLOSURE.ixe --equations EQ.json
--root NAME -o OUT.o` runs ingress, `produce` and `Recheck.run` and writes the
ELF object; `ixcc check-cert` rechecks a certificate. The logic is in
`IxCC.Cli`; the root only calls it. -/
lean_exe ixcc where
  root := `IxCC.Cli.Main

/- Test modules are separate from the production import root. They include the
repository checks and tools (`IxCCTests.Scripts`) and the fixture sources
compiled natively as independent oracles (`IxCCTests.Fixtures.K1` for the Src
differential suite, `IxCCTests.Fixtures.SortPoly` for level-exact relevance,
D18). -/
lean_lib IxCCTests where
  roots := #[`IxCCTests]

/- Src: rules, the K1 table and runs, the native differential, pins,
diagnostics and the bench-k1 entries. -/
lean_exe «tests-src» where
  root := `IxCCTests.Src.Main

/- SrcEval step counts (`docs/source-steps.md`): a closure's root on `Nat`
arguments after `ixcc`'s front end, or every case of a corpus manifest; one
JSON object per run. -/
lean_exe «src-steps» where
  root := `IxCCTests.Src.StepsMain

/- Src rows over the 60 s budget: `ack 3 10`, `fib 30` without primitives. -/
lean_exe «tests-src-slow» where
  root := `IxCCTests.Src.SlowMain

/- The relevance annotator and checker. -/
lean_exe «tests-relevance» where
  root := `IxCCTests.Src.Relevance.Main

/- Lam and erasure: Lam's rules, erasure on
synthetic programs, SrcEval against Lam on K1, bench-k1 and src-sortpoly
(readback, traps, least clocks), the native differential, annotation
mutation, well-formedness and static modes of every erased program. -/
lean_exe «tests-lam» where
  root := `IxCCTests.Lam.Main

/- Regenerates (or with `--check` compares) the K1 artifacts the kernel
evaluates: `IxCCTests/Src/Artifacts/*.lean`, the loaded fib, tak and
gcd programs with their annotations as Lean terms. -/
lean_exe «gen-src-artifacts» where
  root := `IxCCTests.Src.ArtifactMain

/- Anf and the middle-end passes P1–P4: Lam
against Anf after every pass on k1.ixe and bench-k1, the K1 shape
expectations, generated Lam programs under random oracles, WellScoped and
shrink idempotence, and the passes re-run by the kernel. -/
lean_exe «tests-anf» where
  root := `IxCCTests.Anf.Main

/- Fir, the Phase 1 Own fragment and Cfg: every
root and first-order constant of k1.ixe and bench-k1 through Anf → Fir →
Own → Cfg against Anf and Lam (readback, traps, each level's clock map and
timeout clause), the fallback route declined at Fir, generated first-order
programs, the bench entries at test sizes, well-formedness at every level,
and the lowerings re-run by the kernel. -/
lean_exe «tests-fir» where
  root := `IxCCTests.Fir.Main

/- The runtime lowering: `Rt.lower` from Cfg to
Lir on k1.ixe, bench-k1 and generated programs against Cfg (related values,
typed readback, traps, the clock relation, heap and natOverflow), the
primitive sequences at their boundaries, `cx_init`, hand-written cases and
planted mutations; with `--cc`, `Backend.compile` to native objects run at
every level and under `fixtures/x86/runtime_driver.c`; and the lowering
re-run by the kernel. -/
lean_exe «tests-rt» where
  root := `IxCCTests.Rt.Main

/- Plain-RC runtime controls, iterative reclamation and native allocator ABI. -/
lean_exe «tests-rt-rc» where
  root := `IxCCTests.Rt.Rc.Main

/- Exact RC Cfg admission predicates and independently literal evaluator results. -/
lean_exe «tests-cfg-rc» where
  root := `IxCCTests.Cfg.Rc.Main

/- Real-source RC certificates: independent writer/reader processes,
complete list observations, corruptions and same-arena call/drop recycling. -/
lean_exe «tests-rc-certificate» where
  root := `IxCCTests.Recheck.Rc.Main

/- Actual RC pipeline observations and event counts, with independent emitted
object corruption and real-source heap exhaustion controls. -/
lean_exe «tests-pipeline-rc» where
  root := `IxCCTests.Pipeline.Rc.Main

/- Object driver protocol, raw-word release and inter-call memory controls. -/
lean_exe «tests-driver-session» where
  root := `IxCCTests.X86.DriverSession.Main

/- The compiler end to end: the `ixcc` command line on
the bench-k1 closures and k1.ixe (with `--cc`, linked with the runtime driver
and run at test and bench sizes), `produce` + `Recheck.run` against the stage
suites' pipeline, the certificate's JSON round trip, declines, and
certificate mutations (rejected, or code that agrees on every tested input). -/
lean_exe «tests-pipeline» where
  root := `IxCCTests.Pipeline.Main

/- Deterministic x86 step counts: each bench-k1 program's
`cx_init` and root on the typed x86 machine and on `ByteEval`, compared
exactly with the reviewed baseline `fixtures/ixon-v4/bench-k1/steps.json`
(`--write` regenerates it). -/
lean_exe «check-steps» where
  root := `IxCCTests.Pipeline.StepsMain

/- The corpus builder (`docs/corpus.md`): `corpus check` verifies the
frozen fixture families against their `ixcc/corpus/1` manifests
without ix; `corpus rebuild MANIFEST --ix IX` recompiles a family with the
pinned ix and recomputes the expected outputs with Lean's interpreter. -/
lean_exe corpus where
  root := `IxCCTests.Corpus.ToolMain

/- Optional diagnostic report from an external, pinned certified checker.
The kernel itself is neither imported nor a build dependency. -/
lean_exe «certified-census» where
  root := `IxCCTests.Corpus.CertifiedCensusMain

/- The corpus suite: every root of every registered corpus family
compiled, declined with its expected code, or run at every level (SrcEval
… Cfg, Lir, Xv, Xl, typed x86, ByteEval), natively (with `--cc`) and as
standalone executables (with `--exe`) on its frozen cases against Lean's
interpreter. -/
lean_exe «tests-corpus» where
  root := `IxCCTests.Corpus.Main

/- Standalone executables (`ixcc compile --exe`): the layout, the shell, the
writer and its structural check, and with `--run` the executables themselves
(their arguments, failures, confinement and, with `--strace`, system calls). -/
lean_exe «tests-exe» where
  root := `IxCCTests.Exe.Main

/- The ownership and usage-annotation suite, Phase 1 part: the annotated
programs ix accepts against their plain twins and Lean's interpreter at every
level and natively, their code compared, erasure, the Cfg stepper's counters,
the annotator's handling of `0` binders, and ix's recorded verdicts (`fixtures/ownership`). -/
lean_exe «tests-own» where
  root := `IxCCTests.Own.Main

/- Checked plain-RC acceptance, execution, aliasing and complete release. -/
lean_exe «tests-own-plain» where
  root := `IxCCTests.Own.Plain.Main

/- Shrinking and first-divergence reports for the generators: recorded
choice sequences replay to the seeded cases, and a planted bug per generator
(LamGen, FoGen, the Lir generator, the allocation mutants) is found, named at
its level, shrunk and written out as a replayable record. -/
lean_exe «tests-shrink» where
  root := `IxCCTests.Pipeline.ShrinkMain

/- Regenerates (or with `--check` compares) the recheck artifacts the kernel
evaluates: `IxCCTests/Recheck/Artifacts/*.lean`, each bench-k1
closure's `Src.Program`, configuration and certificate as shared Lean terms,
with the typed program and object bytes of the native run. -/
lean_exe «gen-recheck-artifacts» where
  root := `IxCCTests.Recheck.ArtifactMain

/- The recheck path in kernel-evaluable style: building it evaluates
`Recheck.runTyped` on the fib, tak and gcd artifacts and the whole
`Recheck.run` on fib by `decide +kernel`; running it checks every committed
artifact against a fresh ingress, `produce` and native run, and the
recheck path's statistics-free selection against `Select.run`. -/
lean_exe «tests-recheck» where
  root := `IxCCTests.Recheck.Main

/- Ground first-order readback discovery: source instances, emitted layouts,
independent signature validation and malformed candidate rejection. -/
lean_exe «tests-recheck-readback» where
  root := `IxCCTests.Recheck.ReadbackMain

lean_exe «tests-ixon-v3» where
  root := `IxCCTests.IxonV3.Main
  needs := #[.mk (.packageTarget .anonymous `«check-ixon-v3-catalog»)]

lean_exe «check-ixon-v3» where
  root := `IxCCTests.Scripts.CheckIxonV3

lean_exe «check-ixon-v3-catalog» where
  root := `IxCCTests.Scripts.CheckIxonV3Catalog

lean_exe «tests-aiur» where
  root := `IxCCTests.Aiur.Main

/- Lir: kernels, then generated SSA programs checked for well-formedness,
critical-edge splitting, clock monotonicity and exactness, and determinism. -/
lean_exe «check-lir» where
  root := `IxCCTests.Lir.Main

/- Selection: Lir.eval against Xv.eval on the kernels and on generated Lir, in
lock-step (outcome, memory and clock), with per-rule firing counts. -/
lean_exe «check-xv-select» where
  root := `IxCCTests.Xv.Main

/- Allocation: linear scan, the validator and the all-slots fallback on
the kernels and on generated programs, with chaos seeds, validator mutation
and Xv.eval against Xl.eval on every accepted allocation. -/
lean_exe «check-regalloc» where
  root := `IxCCTests.Xv.Alloc.Main

/- Stacking, layout and emission: hand-written Xl, the Lir kernels and
generated Lir to ELF objects, run on the typed machine, the byte machine
and (with `--cc`) natively under `fixtures/x86/backend_driver.c`. -/
lean_exe «check-backend» where
  root := `IxCCTests.Backend.Main

/- The early backend probe: the Lir kernels fib, sumLoop and gcd as ELF objects, with
their static spill and move counts and compile times, for the optional
measurement in benchmarks/meas4 (not a CI gate). -/
lean_exe «backend-probe» where
  root := `IxCCTests.Backend.ProbeMain

lean_exe «check-aiur» where
  root := `IxCCTests.Scripts.CheckAiur

/- Emit deterministic ELF fixtures for the independent object/link gate. -/
lean_exe «x86-object-fixture» where
  root := `IxCCTests.Scripts.X86ObjectFixture

lean_exe «check-x86-encoder» where
  root := `IxCCTests.Scripts.CheckX86Encoder

lean_exe «check-x86-bytes» where
  root := `IxCCTests.Scripts.CheckX86Bytes

lean_exe «check-x86-streams» where
  root := `IxCCTests.Scripts.CheckX86Streams

lean_exe «check-x86-object» where
  root := `IxCCTests.Scripts.CheckX86Object

lean_exe «check-trusted-externs» where
  root := `IxCCTests.Scripts.CheckTrustedExterns

lean_exe «check-tools-tests» where
  root := `IxCCTests.Scripts.CheckToolsTests

lean_exe «check-build-graph» where
  root := `IxCCTests.Scripts.CheckBuildGraph

/- Admission census over an Ixon v4 closure: first rejecting stage per constant. -/
lean_exe census where
  root := `IxCCTests.Scripts.Census

/- Differential check of the local x86 byte model against the host processor. -/
lean_exe «check-x86-hardware» where
  root := `IxCCTests.Scripts.CheckX86Hardware

/- Manual generator for `fixtures/ixon-v4/src-tables.tsv` (runs ix). -/
lean_exe «pin-src-tables» where
  root := `IxCCTests.Scripts.PinSrcTables
  supportInterpreter := true

/- Manual refreeze steps beside `corpus rebuild` and `pin-src-tables`: the
producer pins, ix's fixture package, the erased checker's primitive table,
the typing bundles and the catalogs (runs ix; `docs/corpus.md`). -/
lean_exe «refreeze-ixon» where
  root := `IxCCTests.Scripts.RefreezeIxon
