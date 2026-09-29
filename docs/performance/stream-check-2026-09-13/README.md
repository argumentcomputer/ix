# Indexed stream validation reference — 2026-09-13

At 42 joins, median stream checking takes **418.128 → 0.789 ms**
(**530×**), comparing the retained reference checker with indexed checking
including canonical layout construction. Raw encoding takes **0.288 ms**.
Both checkers receive the same encoded program. The 8,024-byte ELF and all
source identities, observations, and resource-bound goldens are unchanged.

Production emission and linked-stream validation use bounded instruction
windows and cached canonical positions. Lean proves exact acceptance and
rejection equality for arbitrary inputs, and the same `Stream.Valid`
certificate reaches the existing source-to-ELF endpoints. Four new axiom
fences retain the ordinary logical basis; no native interface was added.
[Implementation and proof scope](../../stream-checking.md).

## Phase comparison

Three fresh reference processes use the same fixed matrix: shared/graph pairs
at joins 2 through 9, then graph 10, 12, 16, 24, 32, 40, and 42. Each process
records one invocation per stage, in a fixed order. The table selects graph
rows; all 23 cases and every raw sample appear in [summary.json](summary.json).
Times are medians in milliseconds.

| Joins | Instructions | Text bytes | Raw encode | Reference check | Layout | Prepared check | Indexed check |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 69 | 612 | 0.027 | 2.895 | 0.017 | 0.055 | 0.068 |
| 8 | 177 | 1596 | 0.065 | 20.036 | 0.044 | 0.137 | 0.177 |
| 16 | 321 | 2908 | 0.132 | 67.275 | 0.082 | 0.247 | 0.322 |
| 32 | 609 | 5532 | 0.210 | 246.637 | 0.155 | 0.458 | 0.607 |
| 42 | 789 | 7172 | 0.288 | 418.128 | 0.207 | 0.599 | 0.789 |

From 2 to 42 joins, emitted text grows **11.72×** and complete indexed
checking grows **11.66×**. Across these five points, median indexed
cost is 109.7–110.8 ns per text byte. This supports
size-proportional validation cost on this fixed family; it is not a universal
asymptotic or machine-cost theorem.

At 42 joins, the three-sample ranges are:

| Stage | Minimum ms | Median ms | Maximum ms |
| --- | --- | --- | --- |
| x86-encode | 0.265 | 0.288 | 0.288 |
| stream-reference-check | 415.317 | 418.128 | 422.123 |
| stream-layout | 0.203 | 0.207 | 0.208 |
| stream-prepared-check | 0.594 | 0.599 | 0.600 |
| stream-indexed-check | 0.783 | 0.789 | 0.800 |
| x86-encode-check | 1.049 | 1.077 | 1.077 |

`stream-layout` constructs the canonical tables. `stream-prepared-check`
uses an existing proof-associated layout. `stream-indexed-check` constructs
its own layout and validates once. `x86-encode-check` separately invokes the
ordinary certified production emitter. These intervals overlap in scope;
summing all thirteen recorded intervals would double-count work. The original
eight production intervals remain available for a compiler subtotal.

The reference checker runs before layout/prepared/indexed checking, followed
by ordinary emission and ELF writing. There is no per-stage warm-up or order
randomization. Shared and graph modes use identical objects on their common
inputs. Very short intervals include timer/call overhead; fixed ordering may
influence caches. Timings have no CI acceptance threshold.

## Correctness and scope

All **30 x86_64-linux Nix checks** pass. The byte gate covers **31,921**
instruction forms, their proper truncations, **2,000** patched branches,
**131,084** additional bounded-window inputs, faults, corruption, and actual
runtime-object execution. The stream gate retains its original cases and
checks reference/indexed/prepared results, adding **38** indexed layout cases
through 1,024 instructions. It covers corrupted bytes and offset inventories,
unreachable blocks, invalid calls/tail targets, relocation metadata, resolved
signed endpoints, and overflow.

The reference gate checks **23 persisted replays**, **759 guarded native
calls**, and **184 independent artifact corruptions**. Each worker also runs
2,700 source graph and
3,925 native-certificate mutation
rejections. Every non-timing artifact is byte-identical across the three
processes and matches the existing reviewed report. The consumer recompiles
from canonical persisted IxIR₂ alone and compares exact ELF bytes.

Graph budgets remain 4,096 nodes and 8,192 edges; source block/instruction and
depth limits remain 128, functions 32, allocations 64, and controls 1,048,576.
The graph path still rejects 43 joins at the source block bound. Direct
x86 layout stress fixtures do not change source admission. Existing ISA,
external procedure, compiler runtime, and system linker/loader assumptions
remain as documented in the [trust ledger](../../trusted-extern-ledger.md).

## Process costs and retention

The three whole-worker wall times are **13.21, 13.29, 13.34 s**; peak RSS is
**89,680, 89,828, 89,664 KiB**. These costs include both stream checkers, all compiler phases,
API replay, semantic execution, mutations, inspection formatting, hashing,
artifact writes, and IO. They do not isolate memory for a checker or phase.
The worker now performs additional comparison work, so its process costs are
not a controlled before/after comparison with the earlier graph report.
Generated-program workspace is checked separately by the native harness;
no native throughput measurement is claimed.

Runs use CPU 0, `LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=1`, and `LC_ALL=C`,
after completion of repository builds and checks. Exact host/CPU policy,
tool versions, runtime closure, source/seed hashes, and sampling commands are
recorded in [provenance.json](provenance.json). The reference report covers
one host and three fresh processes.

The raw archive is machine-local and ignored by version control:
`benchmarks/runs/stream-check-2026-09-13.tar.gz` (108,816,226 bytes).
Its SHA-256 is `24360822bbae89e64c3fa4d0c8db285335cdc8532dc100ad90d894ab76c0aa93`. It contains all snapshots, exact
ELF, observations, selection/plan inspection files, raw samples, GNU time
resources, logs, source snapshot, collector, tool identities, executable
seed, and a complete SHA-256 inventory. It has not been uploaded.

| Retained executable | Bytes | SHA-256 |
| --- | --- | --- |
| `check-native-graph` | 120,425,384 | `879673b48bac7c51a267857a6edb218e9faf72b0d34e3ea4dd61be15b9c571c8` |
| `heap-snapshot-object` | 123,580,416 | `2af3591939fe0923e7633a4dc9acdbff5773321e59da1c3084d4a81e2039c044` |
| `native-graph` | 125,037,728 | `ef17850c0dc2ae566943362b298bdbf8e0501a34724eeb039cd7ef0aaced5eb3` |

Replay extracts the frozen source into a fresh directory, verifies all
778 source-file identities and retained seed binaries, then runs
the independent checker and persisted-input recompilation again. Archive
extraction separately verifies every retained member against its inventory.
This is **retained-seed replay**, not a fresh Lean/compiler rebuild.
[Validation evidence](validation.json).

Commands and the measurement-format contract are in the
[native graph protocol](https://github.com/argumentcomputer/Compilatr.ix/blob/jcb/ixby-archive/benchmarks/native-graph.md). After extracting
the archive, its `collect.py replay --repo PATH --raw EXTRACTED-RAW-DIRECTORY`
repeats the recorded replay using the retained seed and recorded tool paths.
Those Nix runtime/tool store paths must still be present.
