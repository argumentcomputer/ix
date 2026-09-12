# Performance

These reports measure the named compiled programs on their recorded hosts.
Each links its raw-result archive, build inputs, correctness checks, and replay
instructions. Compare matching workloads and timing profiles; the current
shared-host references do not establish dedicated regression thresholds.

| Report | Question and scope |
| --- | --- |
| [Native reversal and upstream computations](native-reverse-2026-09-09/README.md) | Runtime list reversal against Lean 4, CakeML, CompCert, GCC, and Clang, plus two unchanged upstream native entries. Reversal is bounded to 64 elements. |
| [Checked counter folding](counter-fold-2026-09-10/README.md) | Paired baseline/optimized reversal, including short-list tradeoffs, code/checking cost, and source-to-object preservation. The baseline remains selectable. |
| [Compiler scaling](compiler-scaling-2026-09-12/README.md) | Bounded source/IR families, phase and process costs, evidence/artifact growth, HPT cache/dependency edits, and exact admission boundaries under unchanged defaults. |

Use the [implemented benchmark protocol](../../benchmarks/protocol.md) to
build, verify, measure, and reproduce the suite. The [benchmark design](../benchmark-plan.md)
defines comparison rules and expansion criteria; the
[roadmap](../roadmap.md#performance-measurement) owns PERF2/PERF3 priorities.
[Interpreter counter evidence](../thesis-counter-evidence.md) complements native
measurements without implying a wall-clock speedup.
