# Performance

## Current reports

Measured on this tree; each report says how to reproduce it.

| Report | Question and scope |
| --- | --- |
| [SrcEval step counts](src-steps-2026-11-10/README.md) | Charged steps (the [unit](../source-steps.md)), their parts and the least clock of every case of the six registered corpus families that the corpus suite runs at the source level, including the benchmark fixtures; raw `ixcc/src-steps/1` lines. |
| [Sparse casesOn as `lazy` rows](sparse-cases-2026-11-12/README.md) | K2 `queue` and the untaken-arm programs natively before and after the change (time, memory, outcomes), SrcEval steps, and every registered root's object and certificate compared. |
| [The producer's cost](producer-2026-11-10/README.md) | `ixcc compile`'s untrusted producer on every committed program and on scaling closures, before and after its super-linear steps were rewritten: stage times, allocation counts, output identity; the timing harness and its raw tables. |

## Historical reports

> **Historical record.** The compiler code, fixtures, runners and documents
> it describes left main on 2026-09-29 when the compiler was rebuilt; links
> to them point to branch `jcb/ixby-archive` of the pre-merge
> `argumentcomputer/Compilatr.ix` repository. Milestone, plan-item and
> section identifiers in it refer to plans that are no longer kept.

These reports measure the named compiled programs on their recorded hosts.
Each links its raw-result archive, build inputs, correctness checks, and replay
instructions. Compare matching workloads and timing profiles; the current
shared-host references do not establish dedicated regression thresholds.

| Report | Question and scope |
| --- | --- |
| [Native reversal and upstream computations](native-reverse-2026-09-09/README.md) | Runtime list reversal against Lean 4, CakeML, CompCert, GCC, and Clang, plus two unchanged upstream native entries. Reversal is bounded to 64 elements. |
| [Checked counter folding](counter-fold-2026-09-10/README.md) | Paired baseline/optimized reversal, including short-list tradeoffs, code/checking cost, and source-to-object preservation. The baseline remains selectable. |
| [Compiler scaling](compiler-scaling-2026-09-12/README.md) | Bounded source/IR families, phase and process costs, evidence/artifact growth, HPT cache/dependency edits, and exact admission boundaries under unchanged defaults. |
| [Modular source certification](modular-source-2026-09-12/README.md) | Six fixed source graphs, source-certificate reuse and fresh checking costs, record sizes, and a fully reachable 611-declaration closure under unchanged monolithic defaults. Descriptive observations without a speedup claim. |
| [Indexed modular assembly](assembly-scaling-2026-09-13/README.md) | Exact baseline/indexed artifacts, cold/unchanged/edit/recovery costs, five assembly widths, and retained replay. Assembly for 611 reachable source declarations falls from 2,180 to 131 ms on the recorded host. |
| [Reused source preparation](source-evidence-2026-09-13/README.md) | Exact baseline/prepared artifacts, canonical-address reuse, fresh checker equality, five preparation widths, and retained recovery. For 611 declarations, source evidence falls from 1,363 to 499 ms cold and from 475 to 41 ms unchanged on the recorded host. |

Use the implemented benchmark protocol (`benchmarks/protocol.md` on the archive branch of the pre-merge Compilatr.ix repository) to
build, verify, measure, and reproduce the suite. The [benchmark design](../benchmark-plan.md)
defines comparison rules and expansion criteria; the
[roadmap](../roadmap.md#measurement) owns measurement priorities.
Interpreter counter evidence (`docs/thesis-counter-evidence.md` on the archive branch of the pre-merge Compilatr.ix repository) complements native
measurements without implying a wall-clock speedup.
