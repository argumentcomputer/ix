# Certified kernel benchmarks

Build the native runner without the host package or its dependencies:

```sh
lake -d IxKernel build --wfail bench-certified-kernel
python3 scripts/bench-certified-kernel.py --output plans/native-baseline.jsonl
```

The default suite records one warmup followed by five fresh-process samples
for each input size. For a focused run:

```sh
python3 scripts/bench-certified-kernel.py --case binders --size 64 --size 128
```

The runner requires Python 3, jj, and GNU time. It snapshots the current jj
working copy to record the measured revision. Build again after changing
Lean sources; output includes source and executable SHA-256 fingerprints,
the compiled Lean version, toolchain pin, architecture, fuel, all samples,
median/range, and maximum process RSS. Measurements do not change CI verdicts.

| Case | Timed operation |
| --- | --- |
| `env` | Admit independent definitions with fresh Nat keys |
| `address` | The same workload with deterministic 32-byte Address keys |
| `references` | Admit definitions repeatedly referring to the oldest entry |
| `binders` | Annotate and check a declaration with nested lambdas |
| `beta` | Annotate and check nested identity applications |
| `context` | Push constant-size domains into the local context |
| `spine` | Weak-head reduce a typed, stuck variable-headed application |
| `ordinary` | Admit Nat/Eq, addition, and repeated recursor-computation theorems |
| `structure` | Admit Prod/Eq and repeated projection-iota/structure-eta theorems |
| `quotient` | Admit the quotient primitives and repeated lift-computation theorems |

Fixture construction happens before the native monotonic timer. The spine
fixture's typing precheck is also outside that interval. Inputs are read
from IO references inside the timed operation, and results are consumed
before it ends. Every declaration workload must accept or the process
fails. The spine must remain unchanged.

Peak RSS covers the entire process, including setup and the spine typing
precheck; it is not an allocation count for the timed operation alone.
The native results are a distinct baseline from the earlier `lean --run`
measurements. Compare like builds, inputs, fuel, and backends, and keep
acceptance coverage separate from execution time.

The standalone strict build also runs the certified fixtures, including
`Tests.Ix.Kernel.SearchOutcomes`. The latter requires low-fuel failures to
decline, with direct malformed-input diagnostics kept distinct. Detailed
operation-count instrumentation remains a separate diagnostic task before
the corresponding performance promotions.

## Retained measurements, 2026-09-29

The P00 baseline is jj revision `457591a8`; the P01 runtime was measured at
`40263091` (change `qlslmuxn`). Both use Lean 4.33.1, native compilation,
fuel 100000, x86_64, one warmup, and five samples per input. The full 37-case
JSONL files are retained locally in `plans/review/native-baseline.jsonl`
and `native-p01.jsonl`, including revision and source/binary fingerprints.
Every declaration workload accepted on both versions.

Separate runs showed large timing variation, including a 3.2× difference
on the unchanged context-push operation. A fresh P00 jj workspace rebuilt
the baseline binary; alternating before/after pairs then measured the
largest input for each case without concurrent builds. Those samples are
in `plans/review/native-p01-paired.jsonl`. Medians below are milliseconds;
RSS is maximum whole-process KiB across the five samples.

| Case / size | P00 ms | P01 ms | P00 RSS | P01 RSS |
| --- | ---: | ---: | ---: | ---: |
| env / 8000 | 329.011 | 301.620 | 11916 | 11924 |
| address / 8000 | 397.293 | 372.827 | 11888 | 11908 |
| references / 8000 | 1425.103 | 1366.757 | 11760 | 11784 |
| binders / 128 | 356.452 | 382.715 | 9588 | 9772 |
| beta / 128 | 0.069 | 0.077 | 9636 | 9632 |
| context / 8000 | 104.799 | 95.323 | 9648 | 9352 |
| spine / 3200 | 59.473 | 62.259 | 9904 | 10708 |
| ordinary / 16 | 2.243 | 2.362 | 9620 | 9532 |
| structure / 16 | 2.135 | 2.334 | 9536 | 9656 |
| quotient / 16 | 4.590 | 4.996 | 9536 | 9636 |

P01 repairs outcomes without changing the search order or fuel allowance.
The paired probes show roughly 5–12% overhead on binder, reduction, and
rule workloads, consistent with additional structured results and retained
normalization causes. The unchanged context control varied by 9%; this is
not a controlled speedup claim. Later performance promotions must retain
the repaired diagnostics and include operation counts.
