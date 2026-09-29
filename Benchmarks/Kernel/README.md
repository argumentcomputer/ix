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
operation-count instrumentation runs separately from native timing.

## Paired runs and diagnostic counts

Build the earlier revision in a separate jj workspace, then alternate
before/after samples of the same input:

```sh
python3 scripts/bench-certified-kernel.py \
  --baseline-binary /tmp/ix-certified-p02/IxKernel/.lake/build/bin/bench-certified-kernel \
  --baseline-revision d09c83b1 --output plans/native-p03-paired.jsonl
```

Both binaries must report identical checksums and compiled Lean versions.
The output records both binary hashes and all samples. Avoid concurrent
builds and other benchmark processes while collecting timings.

Count selected operations in disposable source copies:

```sh
python3 scripts/count-certified-kernel.py --source /tmp/ix-certified-p02 \
  --workdir /tmp/kernel-count-before --output plans/count-before.jsonl
python3 scripts/count-certified-kernel.py \
  --workdir /tmp/kernel-count-after --output plans/count-after.jsonl
```

The work directories must not exist and must be outside their source trees.
The script copies only the standalone package, kernel, fixtures, and runner;
adds a reducible identity wrapper implemented by Lean's `dbgTrace`; and
builds the diagnostic native executable. Existing proofs still elaborate,
but this modified runtime is not the certified production executable.
Source, instrumenter, executable, and before/after instrumented-file hashes
are retained. Diagnostic timing is discarded.

Markers bracket the benchmark action, excluding startup, fixture creation,
and the spine typing precheck. Counts include every outer call (including
fuel-zero calls) of `inferA`, `whnf`, `step`, `isDefEq`, `applyTyped`, and
`annotate`; visited constructors for `liftN`; `spine` visits; `checkSort` and
context pushes; concrete `Env.lookup` calls and key comparisons; and each
rule argument checked inside `applyTyped`. They do not count every lookup
of a temporary functional environment. Tracing can alter compiler
optimization, so use these counts to explain work, and the unmodified
native binaries to measure its runtime effect.

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

## P03 formation reuse, 2026-09-29

P02 (`d09c83b1`) and P03 (measured runtime at `d86b44a7`, jj change
`pnnnlonx`) accepted all 37 configurations at fuel 100000. Five alternating
fresh-process pairs after warmup are in
`plans/review/native-p03-paired.jsonl`; the two action-count runs are in
`count-p02-action.jsonl` and `count-p03-action.jsonl`.

| Case / size | `checkSort` before → after | `inferA` before → after | `liftN` before → after | Rule arguments before → after |
| --- | ---: | ---: | ---: | ---: |
| ordinary / 1 | 18 → 12 | 1247 → 1077 | 6816 → 5914 | 22 → 22 |
| structure / 1 | 34 → 24 | 1743 → 1521 | 7414 → 6724 | 38 → 38 |
| quotient / 1 | 14 → 12 | 2284 → 2214 | 10336 → 10092 | 12 → 12 |

For each published rule, the common type is formed once instead of three
times. Other formation checks remain, explaining the smaller total-count
change. Endpoint checking and rule application remain. Counts for the other
seven cases are identical before/after: explicit local context sharing did
not remove additional measured work, consistent with existing compiler
sharing. No separate context-sharing speedup is claimed.

| Case / size | P02 median ms | P03 median ms | P02 RSS KiB | P03 RSS KiB |
| --- | ---: | ---: | ---: | ---: |
| env / 8000 | 287.669 | 292.334 | 11968 | 12012 |
| address / 8000 | 349.120 | 346.720 | 12012 | 12200 |
| references / 8000 | 1212.283 | 1195.067 | 11792 | 12032 |
| binders / 128 | 323.334 | 322.532 | 9464 | 9484 |
| beta / 128 | 0.098 | 0.106 | 9648 | 9660 |
| context / 8000 | 75.629 | 75.680 | 9356 | 9532 |
| spine / 3200 | 52.248 | 51.270 | 10672 | 10848 |
| ordinary / 1 | 0.982 | 0.898 | 9672 | 9528 |
| ordinary / 16 | 3.288 | 3.165 | 9648 | 9512 |
| structure / 1 | 1.215 | 1.137 | 9528 | 9684 |
| structure / 16 | 3.155 | 3.105 | 9732 | 9616 |
| quotient / 1 | 0.891 | 0.846 | 9696 | 9496 |
| quotient / 16 | 6.752 | 7.033 | 9504 | 9524 |

The admission-heavy size-1 probes improve by about 5–9%; the larger cases
repeat theorem checking after the one-time admission, so formation reuse
accounts for less of their work. The quotient/16 median is 4.2% slower,
with overlapping ranges (P02 4.126–6.836 ms, P03 6.116–7.273 ms).
The unchanged beta probe also varies by about 9%, at sub-millisecond scale.
These measurements support removing repeated formation work, not a blanket
speedup or a demonstrated memory reduction. No cache or entry schema changed.
