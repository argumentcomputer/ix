# Runtime-v2 CSLib: complete native profile and batch tuning

The copied CSLib verifier now has a complete local physical profile, faster
native advice generation, and a measured `cslib-2048` execution class.
The original program, input, output and semantic fuel accounting are unchanged.

The complete native run checks the expected output and **360,337,913 logical
steps**. Its **1,703,268,652 physical microsteps** take 1,633.20 seconds inside the
profiler; process wall time is 27:16 with 9.76 GiB peak RSS and no swaps.
All **5,816 block counts across 672 functions**, plus Eval/Return/Apply counts,
match the independent compiler observer exactly.

The proof experiment below covers a conditional execution segment. A complete
360-million-step CSLib Flock proof remains outside these measurements.

## The same execution, including every join

Both classes prove physical clocks **0–20,000**, covering **4,598 logical steps**.
Their final 57-word statements are byte-identical, including parameters, both
machine states, fuel, clocks, and authenticated memory roots. Each run uses one
proof worker and two Rayon threads on the same Ryzen 9 7950X3D host.

| Measurement | `shared-linked-1024` | `cslib-2048` |
| --- | ---: | ---: |
| Actual leaves | 7 | 3 |
| Actual recursive joins | 6 | 2 |
| Leaf witness + proof + verification | 199.63 s | 87.61 s |
| All recursive proofs + verification | 858.27 s | 290.94 s |
| Total with cached setups | 1,057.90 s | 378.56 s |
| Logical steps/s, including joins | 4.35 | 12.15 |

The measured leaf-and-join total improves **2.79x**, from 17.63 to 6.31 minutes. Including actual setup and fresh-receiver work, the two process totals fall from **25.62 to 13.69 minutes** (1.87x).

Every leaf and recursive node is verified. A separate receiver reconstructs
the selected setup before reading the root proof, verifies it, and rejects
all 114 tested public-word mutations, truncation, and trailing bytes.
The tree follows the production split into a power-of-two left subtree and
the remaining right subtree; all six or two joins are measured directly.

Cached totals exclude setup, source admission, native replay, complete-run
closing and file I/O. The receipts also record process wall time, setup time,
fresh-receiver work and peak memory. This is one bounded timing run per class,
not a full-workload proof-time forecast. The baseline ran alongside native
profiling; quota censuses also overlapped setup work. No other large proof job
ran concurrently with either measured proof tree.

## Why these quotas

Earlier arithmetic and mixed quotas repeatedly filled a rare-family quota
before doing much useful CSLib work. Averaging several phases also failed:
it diluted byte-read and array demand. The tuning experiment therefore uses
the maximum observed per-Fetch ratios from five instruction windows, then
adds capacity for the long builder-copy phases observed elsewhere.

The sweep considers 1K, 2K and 3K Fetch targets; 1,024/1,536/2,048 distinct
cells; and 4,095/6,143/8,191 memory-tree parents. Nine windows informed selection.
The 1K candidate remains a count-only alternative: its smaller leaf requires
more recursive joins. The selected 2K shape retains a positive quota for all
31 families and uses a new fixed transcript domain:
`IxBy/Flock/paged-execution:cslib-2048:v0`.

| Physical bound | Baseline | `cslib-2048` |
| --- | ---: | ---: |
| Microstep slots | 10,432 | 16,062 |
| Memory access slots | 29,248 | 44,950 |
| Distinct cells | 2,048 | 1,536 |
| Shared tree parents | 8,191 | 4,095 |
| Row variables | 16 | 16 |
| State / memory / tree lanes | 16,384 / 65,536 / 16,384 | 16,384 / 65,536 / 8,192 |
| Dense words | 61,691,832 | 60,118,432 |
| Committed words | 67,108,864 | 67,108,864 |

The new class adds useful instruction and builder capacity while reducing
tree padding. It fits the same commitment size. The exact quotas live in
[tuning.rs](../flock-stage3/host/src/ixby/paged_exec/tuning.rs), and the emitter
checks the row capacity of every named class. Class choice remains verifier
policy; it is never inferred from proof bytes.

### Validation across the complete run

The profiler captures 100,000 rows every five million physical steps:
**341 windows, 34.1 million rows, and 7,214,876 logical steps**. These span the
whole native run and cover about 2% of its physical work. Every capture pins
the program and input and retains chip identities, addresses and fuel charges.
It omits values and full machine states and cannot serve as proof advice.

Replaying all captures with the exact circuit quotas and shared-tree counting
gives the following totals. Each window starts a fresh batch sequence and its
last partial leaf is included, so each comparison covers the same work.

| Captures | Baseline leaves | `cslib-2048` leaves |
| --- | ---: | ---: |
| All 341 windows | 12,345 | 5,733 |
| 332 windows outside the selection set | 11,791 | 5,413 |

The complete-leaf occupancy averages, which exclude each partial tail, are
588.60 and 1,280.36 logical steps respectively. These are sampled quota counts,
not an exact full-run leaf count or proof timings.

Four windows use more leaves with the new class because they fill the
4,095-parent bound: starts 555,000,000, 1,645,000,000, 1,655,000,000 and
1,665,000,000. Their baseline/new leaf counts are 24/29, 21/29, 21/27 and 21/26.
The smaller parent budget is a measured tradeoff, not a universal improvement.

## Faster advice generation

The native producer now calculates common numeric operations, constructor
copies, byte windows and scalar byte reads directly. Inverses and the remaining
object/byte cases retain their existing evaluators. These calculations supply
untrusted advice: gate evaluation, Boolean witness constraints, authenticated
memory checks and proof verification retain their full relations.

On the same first million physical steps, native profiling falls from
**14.85 to 1.86 seconds**, about **8x**. Fuel, allocations and chip counts match;
both retained address windows are byte-identical. This is a native-production
measurement, not an 8x improvement in proof time.

Tests compare native results with the Boolean plans, including integer/field
boundaries, every byte-window offset and length, object application and copies,
and a 100,000-step CSLib prefix. The complete native run supplies the independent
output, fuel and block-count check described above.

The streaming profiler drops access-log history after observing each row and
retains current memory values plus bounded capture windows. This avoids keeping
1.7 billion full advice rows resident. The access-discard API is test-only;
these profiling overlays never become proof batches.

## What the full profile changes

| Physical work | Microsteps | Share |
| --- | ---: | ---: |
| Resolve | 493,886,956 | 29.00% |
| Fetch | 303,848,647 | 17.84% |
| Resume, including argument copies | 301,742,966 | 17.72% |
| BuilderCopy + BuilderEmit | 127,974,958 | 7.51% |
| ArrayStep | 63,650,236 | 3.74% |
| Numeric | 58,963,045 | 3.46% |
| Constructor StoreCopy | 38,390,193 | 2.25% |

Fetch/Resolve/Resume together consume **64.55%** of physical rows. The next
interpreter work should reduce operand round trips and argument-entry copying
while preserving exact fuel and source bindings. This does not imply that
64.55% of proof time can be removed: tables, padding, memory routing and joins
have different costs.

The final allocation counters reach 58,068,278 heap cells and 64,855,726 dynamic
byte cells, about 1.93 GiB of byte storage. Builder copying is a substantial
physical cost even though the runtime-v2 primitives already removed the old
reference byte-tree traversal. Avoiding repeated byte materialization in wire
helpers is now supported by direct physical evidence. BLAKE3 contributes
106,369 compression-block microsteps and 3,464 merge microsteps; call counts
alone did not reveal those quantities.

Cheaper consistency arguments and recursive verifier replay remain high
priorities. Quota tuning reduces the number of expensive leaves and joins;
it does not remove their underlying costs.

## Evidence and reproduction

The [complete native report](../flock-stage3/profile/cslib-runtime-v2-native.json)
contains every function's physical costs, progress counters and the complete
capture manifest. The [tuning and proof report](../flock-stage3/profile/cslib-runtime-v2-tuning.json)
checks identical public endpoints and records all leaf/node receipts.
[Archived logs, selected captures and commands](../flock-stage3/profile/cslib-tuning-v0/README.md)
support reproducing both reports.

Validation includes 32 paged-execution tests, 12 memory-log tests, three
execution-tree tests, strict Clippy checks, the complete native run, quota
replays, and the actual leaf/recursive proofs above. The repository's ignored
large-proof tests remain opt-in; these results do not imply that every ignored
test was run.
