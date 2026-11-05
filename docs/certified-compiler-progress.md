# Certified compiler architecture and performance summary

The target is complete certified Lean-to-Ixon compilation of Init+Std in less
than 10 seconds and Mathlib in less than 60 seconds of wall-clock time.
Neither target is met; see "Workload performance" for what has been measured.

## Measurement contract

Measurements use fresh processes on the development host with 32 physical
cores, 64 logical CPUs and about 495 GB RAM. Lean imports are built beforehand;
the command still loads and elaborates its input. All requested declarations,
proof bodies, ordinary metadata, default sharing limits, production checks,
role finalization, output writing and cleanup are retained. No workload Ixon
output cache or partial-output option is used. Timed runs are exclusive.

The current Init+Std workload has 117,694 input declarations and zero compiler
failures. Its complete 253,772,604-byte artifact has Blake3 digest
`a24fd146fcf3c5ed6e6a4821f5f122a6d397270f7eb3106bd7b75ff23eeca9a3`.

## Integrated pipeline components

| Subsystem | Implementation summary |
| --- | --- |
| `Ix.Compile.ReadyCompile` | Dependency-driven ready-queue scheduler with an `O(|E|)` reverse-dependency graph, lock-free atomic work-stealing waves, and a subtype equality bridge (`{ result : ReportResult // result = Ix.Cert.compileReport env }`) discharging `Ix.Cert.checkReport_sound` without re-running sequential `compileEnv`. |
| `Ix.Sharing.Exact` & `Ix.Sharing.FamilyParallel` | Canonical sharing analysis with a pointer-keyed `ExprCache` that checks exact structural equality before a hit (`UInt32` `NodeId` DAG), width-independent tables computed once per constant with the three widths run as parallel tasks on DAGs of at least 1,024 terms (`Exact.TieredFast`, `tieredCandidates_eq`), and parallel exact family tables (`Family.Parallel.exactTable`). |
| `Ix.Cert.Compile` & `Ix.RoleBinding.Compile` | Fused single-pass `recordGraphPar` / `referenceCyclePar` condensation check, incremental post-finalization check fast-path (`FinalizedCheckTasks.spawn` with `added?`), and asynchronous background teardown (`dropAsync`). |

Trace source generation is deferred until the code-generation command requests
it rather than running during unrelated CLI initialization. The integration
also includes implicit `Char` validation and producer-generated native/trace
outputs. The certified compiler is the only compiler
([retired Rust](retired-rust.md)).

## Workload performance

**Current (2026-11-05).** On a 64-core test host under load (load average
35 to 49), `ix compile-lean Benchmarks/Compile/CompileInitStd.lean` compiled
Init+Std to the artifact above in 37.4 s of total wall-clock time (target
`< 10 s`): 29.7 s in `compileReport` and 1.9 s in finalization. There is no
current Mathlib measurement.

**Last recorded Mathlib run (2026-10-29).** A run on an earlier compiler
completed all 783,115 inputs with zero failures: 630.020 s for the full process
(369.915 s main report), 77,311,912 KiB peak RSS, and a 2,349,530,307-byte
output with SHA-256
`458b779888c8f9627bba58d41a3a2cdf48c38eec32d0a4f36606856782c9374a`. The same
checkpoint recorded Init+Std process wall times of 68.62 to 83.18 s.

**Withdrawn figures.** From 2026-10-31 (`d3e3a6f41`) to 2026-11-05 this page
claimed 4.65 s for Init+Std and 44.6 s for Mathlib with `ix compile
--certified`. `ix compile` never had a `--certified` flag: the certified
compiler was already its default. No measurement in the repository's history
supports either figure, which replaced the 2026-10-29 checkpoint (`d511618e0`)
that the previous paragraph quotes. Both figures are withdrawn.

## Verification gates

The gates for this pipeline are the runtime and logical axiom audits
(`lake run check-kernel --with-model`), the source hygiene checks
(`Scripts/SourceHygiene.lean`), the strict compiler and linter gates
(`lake build --wfail`, `lake lint`), the Lean test suites and the Rust crate
tests, with no `sorry` and no new axioms.
