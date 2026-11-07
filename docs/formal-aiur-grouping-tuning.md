# Tuning the certified grouping layout

Measured on 2026-10-27, on `migration/formal-aiur`, against `ade9330c`.
Both application policies now use new Aiur's physical functions and measured
row counts. They replace the direct translation of legacy's grouping policy.
The source programs, bytecode, hints, accelerators, ROMs and fixed tables are
unchanged. This is a grouping/compiler change.

The [CPU scaling follow-up](formal-aiur-trace-scaling.md) measures 1, 8, 32 and
64 threads. New Aiur scales better than legacy on IxVM, but not on the real
recursive verifier; the results below all use eight threads.

## Results

Widths include provider multiplicities, ROMs and fixed tables. Stage two is
counted in base-field columns. Legacy sizes are from the
[previous comparison](formal-aiur-grouping-comparison.md); legacy was not
rebenchmarked for this change.

| Application | Version | Circuits | Stage-one columns | Stage-two columns |
|---|---|---:|---:|---:|
| IxVM | Previous new Aiur | 235 | 9,650 | 4,194 |
| IxVM | Tuned new Aiur | 162 | 8,018 | 3,436 |
| IxVM | Legacy grouped | 222 | 9,163 | 3,616 |
| Recursive verifier | Previous new Aiur | 91 | 4,109 | 1,630 |
| Recursive verifier | Tuned new Aiur | 68 | 3,199 | 1,412 |
| Recursive verifier | Legacy grouped | 84 | 3,880 | 1,590 |

IxVM loses **16.9%** of its main columns; the verifier loses **22.1%**.
Function circuits fall from 214 to 141 and from 77 to 54, respectively.
The same verifier policy also passes certification and integration tests for
aggregation; its additional functions remain separate unless named in the policy.

| Workload | Stage-one cells, before → after | Estimated FFT work, before → after |
|---|---:|---:|
| `Nat.add_comm`, frontier assumptions | 1,322,458 → 1,173,983 | 100,644,448 → 95,655,377 |
| Self-contained 342-constant environment | 46,656,479 → 43,146,214 | 3,527,936,909 → 3,287,192,336 |
| Small recursive fixture | 826,803 → 717,864 | 74,587,165 → 71,212,610 |
| Real recursive verifier | 1,005,868,035 → 937,960,213 | 89,271,866,275 → 84,826,424,989 |

| Workload | Trace + lookups (ms), before → after | Prove (s), before → after | Proof bytes, before → after |
|---|---:|---:|---:|
| `Nat.add_comm`, frontier assumptions | 6.51 → 6.19 | 0.324 → 0.283 | 6,320,763 → 5,478,175 |
| Self-contained environment | 161.11 → 173.34 | 3.618 → 3.400 | 7,227,058 → 6,557,454 |
| Small recursive fixture | 4.74 → 4.41 | 0.214 → 0.206 | 3,585,743 → 2,972,473 |
| Real recursive verifier | 3,552.81 → 3,759.41 | 54.841 → 52.649 | 3,845,899 → 3,168,863 |

All eight proof runs verify. Proving is faster in these runs, and proofs are
smaller. **Large-input trace generation regresses by 7.6% and 5.8%.** The
policy search models padded cells and FFT work, not the CPU cost of evaluating
shared lookup expressions. That distinction matters: fewer cells do not imply
a faster trace writer. This experiment does not isolate the cause of that
remaining runtime regression.

Execution is unchanged by grouping. Its measured medians are retained in the
raw data as a control, not claimed as an execution improvement. They vary
between runs despite identical bytecode.

## What changed

The layout previously multiplied an entire quadratic lookup argument by the
member selector. That makes it cubic, requiring an extra private witness column
and equations. The compiler now recursively chooses lower-degree ways to select
the expression. For example, with member selector `s` and private branch
selector `b`, it uses `(s - b) * x` for `(1 - b) * x`. When the member is active,
`s = 1` recovers the original argument. When inactive, `s = b = 0` silences it.
The emitted expressions still pass the complete row and packet certificates.

For remaining arguments, the private-column heuristic considers whether one
private factor can replace several lifted arguments. It only takes a step that
removes at least as many lifted columns as it adds private columns. The field
interface and maximum polynomial degrees are unchanged.

With memberships held fixed, the layout change alone removes 435 IxVM main
columns and 181 verifier main columns. Two former outliers shrink substantially:

| Original group | Old main columns | New layout, same members |
|---|---:|---:|
| `ixvm_group_08` | 238 | 171 |
| `verifier_group_12` | 378 | 218 |

`Blake3::finish` and `Blake3::compress_block` no longer need their 67 and 84
lifted argument columns. Their private-column counts stay at six and five.

The membership search then uses measured query counts on both workloads for
each application. It tries individual moves, splitting a member back into a
singleton, and whole-group merges, with at most 16 members per group. It accounts
for power-of-two padding, private/shared/lifted width, lookup pairing, auxiliary
columns and quotient degree. Each workload must stay within the starting
layout's cell and FFT budgets. The objective prioritizes normalized FFT work,
then cells, with smaller weights for total columns and circuit count. It is a
corpus-based heuristic, not a global optimum or a promise about every input.

Predicted widths, auxiliary widths, quotient degrees, padded cells and FFT costs
match the actual backend **for every function circuit on all four workloads**.
The search produces only a membership policy. Lean compiles and certifies every
result before it can become an exported layout.

Larger groups also exposed repeated polynomial normalization in certificate
checking. The checker now normalizes equations once and filters equality
comparisons with a structural key. A key match still requires full polynomial
equality. The decidable procedure is proved equivalent to the original
`Implied` proposition; collisions cannot accept an invalid certificate.

## Validation and measurement

The full Aiur proof graph and both application executables build. The grouping
fixture passes freshness, rejection and masked-quadratic regression checks.
The Rust grouping test passes shared-row, padding, sharding and proof checks.
`tools/ixvm/check-formal.sh` passes claims, recursive proving, all thirteen
aggregation shapes and malformed-input rejection. The grouping axiom audit
still reports only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
new axiom or unchecked certificate shortcut was introduced.
Normal IxVM, verifier and aggregation exports match the certified snapshot
results used for benchmarking and integration, with all non-group fields
unchanged from the baseline artifacts.

Measurements use the same fixed inputs as the previous comparison, including
the same 7,232,210-byte inner proof for the real recursive verifier. Both sides
of this before/after comparison use bytecode, `-Ctarget-cpu=native`, eight Rayon
threads and `IX_BENCH_NO_THP=1` on an Intel Xeon 6975P-C. Execution remains
sequential. Two warmups precede five trace samples, or three for the large
recursive workload. Tables show medians. Proving is one verified run per case,
including trace regeneration and verification, excluding execution and key
setup; small timing differences should be interpreted accordingly. FFT counts
are work estimates, not measured FFT time. No CUDA implementation changed or
GPU timing was collected for this tuning.

## Data and reproduction

The [summary](benchmarks/formal-aiur-grouping-tuning/summary.csv),
[every-circuit table](benchmarks/formal-aiur-grouping-tuning/circuits.csv),
[raw timing samples](benchmarks/formal-aiur-grouping-tuning/runs.json) and
[manifest](benchmarks/formal-aiur-grouping-tuning/manifest.json) preserve the
results. The same directory contains both policies, per-function query counts,
layout metrics, singleton shapes and search reports. These files are sufficient
to rerun the membership search without rebuilding or executing IxVM:

```sh
data=docs/benchmarks/formal-aiur-grouping-tuning
python3 tools/ixvm/tune-groups.py "$data/ixvm-metrics.json" /tmp/ixvm-policy.json \
  --prefix ixvm_group \
  --profile "$data/ixvm-counts.json" "$data/ixvm-ungrouped-shapes.json" \
  --profile "$data/environment-counts.json" "$data/ixvm-ungrouped-shapes.json"
python3 tools/ixvm/tune-groups.py "$data/recursion-metrics.json" /tmp/recursion-policy.json \
  --prefix verifier_group \
  --profile "$data/recursion-counts.json" "$data/recursion-ungrouped-shapes.json" \
  --profile "$data/recursion-real-counts.json" "$data/recursion-ungrouped-shapes.json"
```

To tune a changed program, generate a snapshot once, then reuse it:

```sh
lake build ixvm/ixvm multiStark/stark-export aiur/grouping_tune
lake env IxVM/.lake/build/bin/ixvm grouping-snapshot /tmp/ixvm-snapshot.json
lake env MultiStark/.lake/build/bin/stark-export grouping-snapshot /tmp/recursion-snapshot.json
lake env Aiur/.lake/build/bin/grouping_tune /tmp/ixvm-snapshot.json /tmp/ixvm-metrics.json --metrics
lake env Aiur/.lake/build/bin/grouping_tune /tmp/ixvm-snapshot.json /tmp/ixvm-groups.json \
  --policy /tmp/ixvm-policy.json
```

The last command runs the ordinary grouping and partition certificates. Use
`--baseline` to inspect the former layout algorithm. The `compare` Rust example
accepts `--counts-only` to record function query counts, `--ungrouped` to measure
singleton shapes, and `--groups /tmp/ixvm-groups.json` to benchmark a certified
candidate against an existing package. The normal application exports use the
committed policies without additional flags.
