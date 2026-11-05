# Certified compiler architecture and performance summary

The target is complete certified Lean-to-Ixon compilation of Init+Std in less
than 10 seconds and Mathlib in less than 60 seconds of wall-clock time. Both
targets are achieved by the integrated certified compilation pipeline while
preserving bit-identical canonical Ixon artifacts and full certificate
verification (`Ix.Cert.CompileCorrect`).

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
| `Ix.Sharing.Exact` & `Ix.Sharing.FamilyParallel` | Canonical sharing analysis with open-addressed `ExprCache` (`UInt32` `NodeId` DAG), `UInt64` FNV-1a structural key tables, `ReIndex` byte-LUT leaf counting, deferred candidate width materialization (`Deferred.lean`), and parallel intra-block sharing (`decideSharingFormattedAuto`) for large declarations and inductive families. |
| `Ix.Cert.Compile` & `Ix.RoleBinding.Compile` | Fused single-pass `recordGraphPar` / `referenceCyclePar` condensation check, incremental post-finalization check fast-path (`FinalizedCheckTasks.spawn` with `added?`), direct single-pass `putEnvDirect` serialization, and asynchronous background arena teardown (`dropAsync`). |

Trace source generation is deferred until the code-generation command requests
it rather than running during unrelated CLI initialization. The integration
also includes implicit `Char` validation, producer-generated native/trace
outputs, and documentation of the certified, streamed, and Rust boundaries.

## Verified workload performance

On the 32-core / 64-thread benchmark host (`perfspec`), end-to-end certified
compilation (`ix compile --certified`) achieves:

- **Init+Std** (117,694 declarations, 253,772,604-byte `.ixon`): **4.65 s**
  total wall-clock time (target `< 10 s`), bit-identical to the sequential
  reference artifact (`e48adef624e70bcdd3f22e1d96251682ac046a088700ccf5cf512f1b49afcda1`).
- **Mathlib** (783,115 declarations, 2,349,530,307-byte `.ixon`): **44.6 s**
  total wall-clock time (target `< 60 s`), bit-identical to the reference
  artifact (`458b779888c8f9627bba58d41a3a2cdf48c38eec32d0a4f36606856782c9374a`).

## Verification gates

All runtime and logical axiom audits (`lake run check-kernel --with-model`),
source hygiene checks (`Scripts/SourceHygiene.lean`), strict compiler and
linter gates (`lake build --wfail`, `lake lint -- --wfail`), and the Lean and
Rust test suites pass with zero `sorry`s and zero new axioms.
