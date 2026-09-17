# Fused interpreter steps with exact execution boundaries

The optional `cslib-fused` execution class combines common operand, consumer
and argument-copy sequences into one circuit row. Across 341 captured CSLib
windows it removes **45.47% of execution rows** and **16.71% of memory events**.
The original program, logical fuel and public boundary state remain unchanged.

The smaller layout has half the padded leaf commitment, but needs more leaves
across most captured phases. It is an explicit class choice, not a new default.
Counts and a bounded proof comparison do not establish a full CSLib speedup.
On the matched 20,000-original-step proof tree, leaf work plus every join falls
from **128.88 to 86.63 seconds**, a **32.8% reduction** in this run.

## Checked compositions

Every composition invokes the existing instruction, operand, numeric and frame
relations. Their complete intermediate states are connected by circuit wires.
The new code does not replace those relations with unchecked native shortcuts.

| Sequence | Original rows | Fused rows | Memory events, before → after |
| --- | ---: | ---: | ---: |
| Fetch, resolve one operand, control instruction | 3 | 1 | 8 → 7 |
| Fetch, resolve two operands, binary numeric instruction | 4 | 1 | 13 → 10 |
| Two argument/object copy steps | 2 | 1 | 6 → 4 |
| Fetch, resolve `n` arguments, call, copy arguments (`0 ≤ n ≤ 4`) | `2 + 2n` | 1 | `5 + 6n` → `3 + 4n` |

[The implementation](../flock-stage3/host/src/ixby/paged_exec/fusion.rs)
retains scratch writes and forwards their checked values into consumers.
An exact equality gate compares the complete address and both 128-bit value
words of each omitted read with the corresponding write. Its XOR residuals
are constrained to zero; it uses no probabilistic fingerprint. Omitted dummy
events have their address, read/write flag and both value words bound to zero.
Each fused batch also authenticates address zero with both its old and new
values constrained to zero. Binding a dummy read's wires alone would leave
that cell unchecked for an arbitrary starting root. The reserved cell counts
against the fixed cell quota and adds no execution event. Thus the invariant
is checked even when a batch contains no remaining dummy read.

The fused emitter keeps fixed input constants and zero-valued output checks
in separate wire classes. This avoids cycles and a pinned-builder limitation:
later gate inputs do not automatically follow a wire's earlier alias.
The zero-cell checks use actual equality gates, and a regression inspects the
compiled circuit's connections to memory cells and fixed public zeros.

Calls resolve **all arguments before writing any callee local**. This preserves
arguments in recursive and tail calls that reuse the caller's local bank.
The function declaration, arity and continuation write remain checked. Larger
calls, other instructions and partial sequences retain the ordinary path.
Unary numeric operations are not included in the binary numeric composition.

Scratch writes deliberately remain authenticated. This preserves the original
memory root at every completed composition and permits direct comparison with
the ordinary interpreter at the same original microstep boundary. The saved
work is redundant reads, dummy events and intermediate state-routing records.

### Clocks, ordering and padding

The public clock continues to count **original microsteps**. A fused row
advances it by a setup-selected positive span of 2, 3, 4, 6, 8 or 10. New
clock gates check every increment and reject overflow; a witness cannot select
its span. Exact full-state matching and strictly increasing clocks retain
one chain from the public seed to the public seal.

Memory events use the composition's start clock and their ordered event
positions. Each composition has fewer than 32 events. Their order agrees with
the original sequence, while the next composition starts at a greater clock.
The existing memory chronology, value and shared-tree authentication checks
therefore apply without requiring a memory event at every clock value.

An exact requested stop inside a possible composition falls back to ordinary
rows. Every existing suspended-instruction boundary remains available, and
fuel charges still come from the original checked steps. Inactive rows retain
canonical zero advice. New classes have distinct setup domains; the existing
`cslib-2048` setup and proofs retain their identities.
If a composition alone exceeds a tiny class's memory capacity, the producer
also falls back to ordinary steps so that the class can make progress.

## Circuit size and captured phases

The census reuses the address captures from the
[complete native run](IxbyCslibTuning.md). They span the workload at five-million
microstep intervals. Each of 341 windows contains 100,000 original microsteps;
the samples total 34.1 million steps, not one continuous execution.

| Count across all windows | Original | Fused |
| --- | ---: | ---: |
| Execution rows | 34,100,000 | 18,593,243 |
| Memory events | 94,511,058 | 78,715,341 |

The counter recognizes only complete checked sequence shapes and removes the
same read/dummy positions as the circuit. It checks the resulting sequence
against actual native compositions in differential tests. Captures contain
addresses and fuel counts, not values; these replays are **counts, not proofs**.

| Compiled capacity | `cslib-2048` | `cslib-fused` | Larger fused candidate |
| --- | ---: | ---: | ---: |
| Execution row slots | 16,062 | 7,780 | 15,918 |
| Memory event slots | 44,950 | 30,441 | 59,750 |
| Distinct cells / shared parents | 1,536 / 4,095 | 1,152 / 4,095 | 1,536 / 4,095 |
| State-routing lanes | 16,384 | 8,192 | 16,384 |
| Memory-routing lanes | 65,536 | 32,768 | 65,536 |
| Dense circuit words | 60,118,432 | 32,766,760 | 63,750,872 |
| Padded commitment words | 67,108,864 | 33,554,432 | 67,108,864 |
| Leaves across all windows, including each tail | 5,733 | 9,331 | 5,479 |
| Windows with fewer / equal / more leaves than baseline | — | 1 / 3 / 337 | 167 / 66 / 108 |

The small layout stays below both routing thresholds: its 30,441 event slots
plus twice its 1,152 cells require 32,745 memory records, just below 32,768.
Its quota reductions increase the captured leaf count **62.76%**. The larger
candidate reduces leaves only **4.43%** overall and increases dense words; it
is count-only and is not an approved proof class. Fewer useful rows alone do
not guarantee cheaper padded circuits or fewer recursive joins.

Quotas started from the preselected captures at clocks 0, 55 million,
115 million, 195 million and 380 million, followed by padding and prefix
experiments. All 341 windows were then replayed, including adverse phases.
The full report retains every window's counts, quota stops and source receipt.
`Numeric`, small call families and builder copying remain significant limits;
further class tuning needs broad-phase validation and equal-work proof trees.

## The same execution, including every join

Both newly measured trees cover original microstep clocks **0–20,000** and
logical fuel **0–4,598**, using the unchanged runtime-v2 program and input.
Both contain three actual execution leaves and two recursive joins. Their
complete 57-word public statements are byte-identical, including all state
words and memory roots. The fused path uses **10,002 circuit rows** and
**45,895 memory events**, versus 20,000 rows and 56,062 events.

| Measured work | `cslib-2048` | `cslib-fused` |
| --- | ---: | ---: |
| Leaf witness generation, proving and verification | 92.76 s | 51.64 s |
| Join of the first two leaves, including verification | 19.22 s | 18.43 s |
| Join of that node with the third leaf, including verification | 16.90 s | 16.56 s |
| Leaves plus every join, with cached setups | **128.88 s** | **86.63 s** |
| Leaf process wall time, including setup | 217.53 s | 94.95 s |
| Tree process wall time, including setup and fresh receiver | 339.82 s | 170.67 s |
| Combined process wall time | **557.35 s** | **265.62 s** |
| Leaf peak RSS | 31.45 GiB | 18.34 GiB |
| Tree peak RSS | 34.54 GiB | 30.69 GiB |
| Final root proof | 404,083 bytes | 406,323 bytes |

The cached comparison improves **1.49x**; combined process wall time improves
**2.10x**, with **41.7% lower leaf peak memory**. Cached totals exclude setup,
source admission, complete-run closing and I/O. Process totals include actual
setup and fresh reception; they still cover a conditional execution segment,
not a complete source-to-output CSLib proof.

Both classes use one worker and two threads on the Ryzen 9 7950X3D host.
The baseline uses the pinned v10 binaries; the corrected fused proofs use v14.
The later changes affect fused zero-cell wiring and its regression test;
the baseline class remains unchanged. Large proof jobs run sequentially
with an 84 GiB cap and no swap. Final address counting finishes before the
corrected fused proof measurements. These are **one run per
class**; the timing variation visible against earlier runs is another reason
to keep the conclusion bounded to this matched measurement.

The ordinary class reproduces its earlier root proof byte for byte. Its
SHA256 remains `740e4e4ed6e444f162ce959c8e98c6aeeae3bf1f1a20864be87c435f1a5251bf`.
The fused root uses its new setup and has SHA256
`65d23104320e07d1224f0a640683476aec03af080ab7431762b51406c668edb6`.
Both fresh receivers rebuild the approved setup and accept the root before
running mutation and framing rejection checks.

## Validation

Seven new ordinary fusion tests exercise the actual composed circuits, native
execution and authenticated batches. They cover control and numeric operands,
all call arities 0–4, ordinary/self/tail/recursive-tail calls, reversed arguments
in overlapping local banks, heap and scratch copies, final partial copies,
maximum 64-element vectors, disabled rows and exact stops inside compositions.
The compact-class regression also checks a four-argument call whose 257 shared
parents exceed that class's 255-parent capacity: ordinary rows make progress
through authenticated batches and reach the identical final state and root.
Mutations target instruction data, arity, fuel, state and both halves of
forwarded values. Separate clock tests cover every supported span, high words,
overflow and noncanonical inactive inputs.
The reserved-cell test changes either value word and constructs a tree that
omits address zero entirely; the fused batch circuit rejects each case.
It also inspects the verifier's wire classes, so a witness-only check cannot
satisfy the regression.

A 100,000-original-step CSLib differential replay compares every composition's
state, write order and touched cells with the ordinary path, then checks equal
final memory roots. It uses 46,561 rows and 226,162 events, versus 100,000 rows
and 280,116 events. A separate 10,000-step replay also compares accelerated
native advice with the existing Boolean plans.

The ordinary paged-execution suite passes 39 tests, execution ordering passes
10, memory logging passes 12, and recursion passes five. Strict Clippy passes
for both workspaces.
Large ignored proofs remain opt-in. The measured trees check genuine leaf and
recursive proofs, and fresh receivers reject all 114 tested public-word
mutations, truncation and trailing bytes. Native constraint-to-reference
refinement and a complete CSLib proof remain separate obligations.

The [machine-readable report](../flock-stage3/profile/cslib-runtime-v2-fusion.json)
checks the capture receipts, every batch's counts, exact public boundaries and
every recursive join. [Logs, roots and reproduction commands](../flock-stage3/profile/fusion-tuning-v0/README.md)
record the measured source and binaries.
