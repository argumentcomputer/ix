# Checked reserve/reuse counter folding

The first bounded PERF3 experiment delivers a checked reserve/reuse counter
fold with a **1.3621× paired entry speedup** and **1.1829× paired lifecycle
speedup** at length 64 with primary payloads on the recorded host. Reversal
code shrinks from **1,036 to 952 bytes**. The fold is available as an explicit
native selection option, with the original baseline still the default.

The [generated report](report.md) retains all 38 comparisons; the
[machine-readable summary](summary.json) includes full numerical results,
session medians, uncertainty, process memory and checking costs.
This experiment follows the
[PERF1/C3 reference](../native-reverse-2026-09-09/README.md). It compares two
native lowerings of the same runtime reversal source using the original
driver, input matrix, allocation/reclamation contract and measurement profiles.

Collection ran from **2026-09-10 16:31:49 UTC to 18:14:31 UTC**. All **30
paired blocks in three sessions** passed on their first attempt, with **6,840
accepted samples**, no retries, missing rows or discarded slow observations.

## Runtime results

At length 64 with primary payloads, times are nanoseconds per operation:
the median across 30 block medians, followed by its 95% bootstrap interval.

| Profile | Baseline ns [95% interval] | Folded ns [95% interval] | Paired speedup [95% interval] |
| --- | ---: | ---: | ---: |
| Entry plus bounded handoff | 235.00 [233.88, 236.02] | 172.13 [167.45, 173.44] | 1.3621 [1.3566, 1.4019] |
| Fresh allocation lifecycle | 417.00 [413.50, 423.66] | 357.75 [349.11, 359.84] | 1.1829 [1.1747, 1.1932] |

Ratios divide baseline time by folded time within each paired block; values
above one favor folding. Their median need not equal the ratio of independently
aggregated time medians. Lifecycle includes construction, reversal, an
order-sensitive digest and complete reclamation. Entry timing includes the
call and bounded output handoff, with fresh construction, full checking and
release outside each timed chunk.

All 36 nonempty rows favored folding in their point estimates and pointwise
95% intervals. At length 1, primary entry time was 10.70 to 9.84 ns, with a
paired ratio of 1.0881 [1.0824, 1.0914]; lifecycle was 24.46 to 23.12 ns,
with a ratio of 1.0541 [1.0400, 1.0661]. The length-64 large-Word rows also
favored folding: entry ratios round to 1.36, and lifecycle ratios to 1.17–1.19.
The full report retains every short-list and payload-boundary comparison.

Empty-list lifecycle time was 20.87 to 20.74 ns, with a paired ratio of
1.0099 [0.9968, 1.0173], which does not resolve a difference. Empty entry time
was 7.63 to 7.40 ns. The empty path executes no folded cons body; code placement
and run conditions remain possible causes of its small timing shifts.

These are results for one bounded workload on one shared host. The 38 rows
are related input cases, and their pointwise intervals are not a claim about
independent applications or a simultaneous confidence band. The five external
PERF1 implementations were not remeasured in this paired experiment.

## The checked change

The baseline cons body increments the reservation counter and decrements
the live counter, then reverses both changes in the adjacent reuse operation.
Each counter change is a load, arithmetic instruction and store. Removing
these four cancelling changes saves twelve instructions per consumed cell.
The matched [C kernel](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/benchmarks/native/arena_kernel.c) does not
perform these intermediate counter changes. That comparison identifies a
specific experiment; it does not establish the cost of this rewrite.

The folded body retains all cell loads and stores, including the temporary
reserved tag and the store of the original head, plus the cumulative reuse
and payload counter updates. This experiment does not also change addressing,
validation, loop dispatch, allocation, release or the driver.

| Static property | Baseline | Counter fold |
| --- | ---: | ---: |
| Cons-body instructions | 28 | 16 |
| Complete reversal entry, local steps | `42n + 82` | `30n + 82` |
| Reversal `.text` bytes | 1,036 | 952 |
| Native allocation / reuse / RC effects | Same | Same |

The `UniqueCounterFold.state_eq` theorem proves equality of every final
general-purpose register and arena word for arbitrary initial counter values.
Its `trace` theorem supplies the actual instruction effects to the reusable
loop proof. The source, physical-target, native execution and parsed-object
interfaces quantify over the selected variant. Trap exclusion covers every
instruction prefix; resource correspondence observes the combined reserve/reuse
operation at its completion. The folded body exposes no intermediate
reservation-accounting boundary. The existing exclusive-arena, exact Word,
return-slot, source sharing/oracle and ISA/linker assumptions remain explicit
in the [runtime specification](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/docs/source-native-runtime.md).

The default selector remains the original baseline. `Native.select compilation
true` or the fixture's `--counter-fold` option selects the folded body. Each
variant has its own checked object/provenance identity. The original source
and canonical IxIR₁ identities agree, and preflight comparison found the
baseline's complete artifacts and linked executable byte-identical to PERF1.

## Code, memory and checking costs

| Variant | Reversal / release `.text` bytes | Pipeline JSON bytes | Producer wall s / peak RSS KiB | Independent gate wall s / peak RSS KiB |
| --- | ---: | ---: | ---: | ---: |
| Baseline | 1,036 / 231 | 89,193 | 13.58 / 85,604 | 28.02 / 85,536 |
| Counter fold | 952 / 231 | 84,188 | 10.66 / 83,144 | 21.17 / 84,024 |

The reversal is 84 bytes (8.1%) smaller. Generation and independent-gate
CPU/wall/RSS records are single diagnostic envelopes. Generation includes
modeled fixture executions; each gate includes two fresh generations,
decoding, corruption regressions and a linked native harness. The shorter
execution and observation traces are part of these envelopes. These numbers
do not isolate compiler or proof-checker phases or establish a statistical
checking-speed improvement. Complete CPU and command records are retained.

Both variants had median ready RSS of 2,028 KiB and maximum recorded process
high-water RSS of 11,104 KiB. Sample RSS ranged from 2,192–2,464 KiB for the
baseline and 2,188–2,464 KiB for folding. Logical allocation, reuse, RC,
occupied arena size and complete reclamation are unchanged; this is a code
and runtime improvement with no claimed source-space saving.

## Measurement and checking contract

The [paired protocol](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/benchmarks/counter-fold.md) freezes 38 timing
rows, two profiles, common operation counts, 30 paired blocks, three sessions,
three samples per variant/block/row, and 10,000 hierarchical paired bootstrap
draws. All 6,840 accepted samples are retained. The short-list and large-Word
rows remain in the comparison. The host is shared; no timing threshold follows
from this experiment.

Each actual benchmark artifact set is compared byte for byte with the
independent gate's freshly checked artifacts. Each variant passes eight
runtime inputs, 203 malformed calls, full reclamation and twenty deliberate
artifact/observation corruptions. Its timing executable also passes every
one of the 585 scalar inputs and 19,305 input/capacity combinations, with
complete arena observations equal across variants. Smoke runs exercise all
76 variant/row combinations and reject malformed timing observations.

The AMD Ryzen 9 7950X3D host ran Linux 7.1.2/NixOS, microcode `0xa60120a`,
with worker CPU 2, controller CPU 0 and NUMA node 0. SMT was enabled and the
worker's sibling CPU 18 was unreserved. The observed governor was `powersave`
under `amd-pstate-epp`, with boost enabled and the `tsc` clocksource. Native
timing used `CLOCK_MONOTONIC_RAW`. Other tenants and thermal conditions were
uncontrolled. Three session clusters limit inference across days or machines;
this run sets no CI timing threshold.

Before measurement, all **813 Lake build jobs**, the compiled regression,
stream/object and tool/trust checks, and all **19 x86_64 Linux Nix checks**
passed. The four added axiom fences preserve the existing logical basis.
Both native artifact gates and both complete benchmark correctness matrices
passed. A deliberately cross-selected supplied artifact set was rejected.
Every accepted sample passed the frozen duration, clock, RSS and environment
checks; analysis reconstructed all combined samples from their raw process,
schedule and executable identities and passed its corruption checks.

The retained-source replay extracted and checked **491 source files**, rebuilt
both objects and executables with an empty environment plus recorded variables
and hashed tool seeds, repeated the complete correctness matrix, and regenerated
analysis from the original raw process records. The build manifest, artifacts,
executables, correctness results and both analysis files matched exactly.
See [reproduction.json](reproduction.json). Replay uses the same host and pinned
Nix closure; it does not require new clock readings to equal old ones or claim
a second physical host. The source snapshot predates final results prose and
a scope clarification in an axiom-fence comment; executable code, proofs,
protocol and analysis choices were frozen before measurement.

## Follow-up decision

This delivers one bounded checked optimization experiment in PERF3. Explicit
fold selection is supported by source-to-object preservation, the complete
correctness matrix and the positive paired results. The baseline remains the
default and a byte-identical selectable reference. Broader compiler scaling,
cache/dependency-edit experiments and a general external peephole proposal
checker remain separate work.

The next capability extension remains N3's runtime scalar arguments,
branches/joins and direct calls, with exact Nat/Word ranges and F1 stack/space
contracts where needed. Additional lowering changes should each carry their
own proof and paired measurement. These fixture envelopes provide no reason
to raise I3 source-certificate budgets. General PAP specialization, field
deletion, unboxing and broader PERF2 workload admission retain their existing
gates.

## Retention and replay

The full bundle is retained locally at
[`benchmarks/runs/b2c2282c4023e9652c7e3b661492502153e2b61368fbc639edd9eb7f3cf37c12.tar.gz`](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/benchmarks/runs/b2c2282c4023e9652c7e3b661492502153e2b61368fbc639edd9eb7f3cf37c12.tar.gz),
SHA-256 **`b2c2282c4023e9652c7e3b661492502153e2b61368fbc639edd9eb7f3cf37c12`**,
**327,761,672 bytes**. Copy that complete archive when moving the evidence to
another storage service. The raw archive is excluded from Git; the report,
summary, reproduction result and [retention record](retention.json) are tracked.

The archive contains frozen source/tool inventories and seeds, both object
and executable sets, complete correctness and smoke results, pilot/frozen
schedules, all raw samples and environment observations, diagnostic costs,
fresh-source replay and validation logs. `reference/SHA256SUMS` covers 1,196
files; the archive digest also covers the checksum inventory itself. A fresh
extraction passed every checksum, and its relocated runner regenerated the
report and summary byte for byte.

From the repository root, in the pinned environment and using fresh paths:

```sh
archive=benchmarks/runs/b2c2282c4023e9652c7e3b661492502153e2b61368fbc639edd9eb7f3cf37c12.tar.gz
printf '%s  %s\n' b2c2282c4023e9652c7e3b661492502153e2b61368fbc639edd9eb7f3cf37c12 "$archive" | sha256sum --check -
mkdir /tmp/ixcc-counter-fold-retrieved
tar --no-same-owner --no-same-permissions -xzf "$archive" -C /tmp/ixcc-counter-fold-retrieved
/tmp/ixcc-counter-fold-retrieved/reference/run.sh verify-bundle
/tmp/ixcc-counter-fold-retrieved/reference/run.sh analyze /tmp/ixcc-counter-fold-analysis
/tmp/ixcc-counter-fold-retrieved/reference/run.sh reproduce /tmp/ixcc-counter-fold-reproduction
```
