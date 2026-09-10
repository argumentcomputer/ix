# Trace-sharding performance and integration audit

Date: 2026-09-10. Scope: recommendations from ix PRs 623, 624, 625 and 621,
CPU SIMD quotient-buffer reuse, and their interaction with single-claim
distributed execution and range-sum recursion.

This is a source review and implementation recommendation, not a completed
soundness proof or a new benchmark. No builds, tests, benchmarks, production
configuration changes, or implementation edits were performed for this audit.
Numbers below are attributed to their published measurements; proposed
validation is work for a later implementation, not work performed here.

PR descriptions and benchmark comments were read from GitHub; selected source
diffs were then checked in an isolated temporary Git clone. Prover dependencies
were read from their already-present pinned Cargo checkouts. Existing repository
branches and indexes were not changed. This document is the only workspace edit.

## 1. Snapshots and bottom line

| Source | Reviewed revision | Status when read |
| --- | --- | --- |
| [PR 623: sb/cluster](https://github.com/argumentcomputer/ix/pull/623) | `fa67a34d3554e499dfc8a106d9149203b4eff3d9` | Open, draft |
| [PR 624: delayed let inference and linear multiplication rows](https://github.com/argumentcomputer/ix/pull/624) | `849d2acf21753743a0c6067bcba1fccdabbe20df` | Merged; merge `aece4d02638eb1c1267490ec718a5d1f5c343ba1` |
| [PR 625: targeted FFT regression fixtures](https://github.com/argumentcomputer/ix/pull/625) | `173c1b5e20c276eb68e1dcb45fb52dc7de2bb63e` | Merged; merge `5430a5d9be08bd85588547053484c5030d6bed23` |
| [PR 621: execution storage, setup and refinement](https://github.com/argumentcomputer/ix/pull/621) | `3e7586a7adb0c6f3cd3ff5854da832701288ec90` | Open; full FLT execution still reported pending |
| Current document workspace | `/home/ubuntu/ix`, `sb/aiur-trace-sharding-design`, `ab627cd6` | Existing worktree changes preserved |
| Distributed/range implementation | `/home/ubuntu/ix-work`, `sb/aiur-distributed-execution`, `a4d1e914` plus uncommitted range changes | Moving WIP snapshot, not an immutable PR revision |
| CPU prover dependency | multi-stark `2042565be1939cf2bef4b0d4d47ba3354473c5bf` | Pinned by the local ix workspace |
| Matrix/SIMD dependency | Plonky3 `3152b14a89067c83775a8076cc262ffc48a1fd7c` | Pinned by that multi-stark revision |

Keep the single logical claim and range-sum proof algebra. Borrow the cluster
PR's resource placement and scheduling techniques, not its environment-claim
partitioning as the required production architecture. Pursue SIMD scratch reuse
as a separate, relatively low-risk CPU optimization. Bring the merged kernel
changes and their regression fixtures together. Port PR 621 selectively: its
memory and scheduling ideas are useful, but its public post-rebase performance
results do not support adopting the whole branch as a universal speedup.

### Priorities

P1 means fix before relying on the affected resource/correctness contract;
P2 means a high-value implementation or integration task; P3 means a later,
measurement-dependent change. These are adoption priorities, not CVSS ratings.

| ID | Priority | Recommendation | Main effect / caveat |
| --- | --- | --- | --- |
| A1 | P1 | Correct grouped-circuit row accounting | Both 623 and 621 contain the same essential fix; port once |
| A2 | P1 | Use one admission budget across outer slots, range nodes and retained records | Prevent nested concurrency from multiplying the RAM allowance |
| A3 | P2 | Use NUMA-local proving lanes and bounded lookahead | Transfer 623's throughput gains to independent trace-shard work |
| B1 | P2 | Reuse SIMD quotient scratch across packets | Fewer allocations; no intended constraint, transcript or proof-format change |
| C1 | P2 | Integrate 624 together with 625 | Removes targeted execution/trace work; changes circuits and verifier identity |
| D1 | P2 | Port native setup and completion-driven dispatch from 621 selectively | Preserve complete input validation and record-lifetime accounting |
| D2 | P2 | Evaluate compact records and prehashed keys separately | Lower storage can come with slower execution; adapt pointer namespaces |
| E1 | P2 | Cache individual range nodes; schedule joins on completion | Resume partial trees and remove batch/level barriers |
| E2 | P2 | Size ranges by verification cost and optimize active circuit width | Fixed shard count and small statements do not guarantee small proofs |
| E3 | P3 | Replace repeated full-preamble processing with an authenticated compact context | Coordinated protocol change, justified as batch sizes grow |
| M1 | P2 | Separate setup, native verification and recursive verification metrics | Avoid treating a five-second CLI invocation as a five-second STARK check |

## 2. PR 623: what transfers to trace sharding

### 2.1 Interpret the measurements correctly

The reported Mathlib run used 246 leaves on an r8i.metal-48xl with three NUMA
domains. The before/after results were:

| Metric | Previous run | Rebased run |
| --- | ---: | ---: |
| Stage 1 | 2 h 38 min | 2 h 44 min |
| Stage 2 | 3 h 25 min | 1 h 52 min |
| Reported total proving | 6 h 20 min | 4 h 36 min |
| Root proof | 9.85 MB | 4.91 MB |

The new root covers 679,499 constants with no remaining assumptions. The PR
attributes proof-size reductions to main's function grouping, not NUMA alone.
It reports three isolated lanes scaling about 3x, versus about 1.7x for
unpinned concurrent slots; transparent huge pages improved its prover runs
about 1.5–1.7x. These are workload/machine-specific reports, not multipliers
to multiply into a trace-sharding forecast. The old stage times sum to
6 h 03 min, not the reported 6 h 20 min; the unexplained difference should
remain visible rather than be silently reconciled. [PR 623 results](https://github.com/argumentcomputer/ix/pull/623)

The user-supplied run table additionally reports 1,207 GiB slice peak and
at most 425 of 504 GiB resident per NUMA node in the new run. That distinction
matters: a machine can have free RAM overall while a strictly bound node
cannot satisfy another allocation.

### 2.2 A1: fix grouped row estimates before tuning budgets

The local `crates/aiur/src/synthesis.rs::raw_of` uses a circuit index to look up
one function's query count. Grouping invalidates that correspondence. A grouped
circuit's raw row count must sum its member functions first, then apply any
hypothetical subdivision and trace padding. PR 623 implements that correction;
PR 621 independently includes it. These are overlapping fixes, not additive
optimizations. [623 estimator](https://github.com/argumentcomputer/ix/blob/fa67a34d3554e499dfc8a106d9149203b4eff3d9/crates/aiur/src/synthesis.rs#L120)

In the local trace branch this matters even though `shard.rs::circuit_rows`
already uses `function_rows`: `prove_ixvm_within_budget` first gates on the
whole-record estimate. A wrong estimate can unnecessarily split a fitting job
or skip trace sharding for a job that does not fit. The range wrapper inherits
that gate. Correct the entry gate as well as the shard-specific estimator.

Keep conservative treatment of zero-multiplicity hint entries distinct from
the indexing bug. Exact active-row estimates are a separate improvement, and
inactive proof rows do not imply that their retained execution data is free.

### 2.3 A2/A3: one resource model, NUMA-local lanes, bounded overlap

PR 623 creates a Rayon pool per NUMA domain and pins both pool workers and
serial producer threads. Its scheduler reserves memory per process and per
node, including the prepared-next record. That is a better template than
independently increasing execution threads, proof threads and range-tree jobs.
Its constants, including a 40 GiB lookahead allowance, are calibrations for
its measured environment-join shapes, not constants to copy for trace ranges.
[NUMA implementation](https://github.com/argumentcomputer/ix/blob/fa67a34d3554e499dfc8a106d9149203b4eff3d9/crates/ffi/src/numa.rs#L248),
[pipeline reservations](https://github.com/argumentcomputer/ix/blob/fa67a34d3554e499dfc8a106d9149203b4eff3d9/crates/ffi/src/aiur/aggregate.rs#L2069)

Recommended transfer:

- Run independent trace-shard commitments and second-pass proofs on admitted
  NUMA-local lanes. The pinned multi-stark `prove_batch_with` currently uses
  sequential iteration for both passes; shard-internal parallelism is not
  batch-level concurrency. Preserve deterministic shard indices when collecting
  parallel results. [Batch driver](https://github.com/argumentcomputer/multi-stark/blob/2042565be1939cf2bef4b0d4d47ba3354473c5bf/src/batch.rs#L457)
- Account for live worker records, retained stage-one commitment data, current
  witness/prover buffers, SIMD scratch, queued records and unconsumed proofs.
  Charge shared data once globally, but also account for its actual local
  residency where node capacity is the limiting resource.
- Move records into consumers instead of copying them. PR 623 explicitly
  transfers a prepared record into proving; preserve that ownership discipline.
  [Prepared execution handoff](https://github.com/argumentcomputer/ix/blob/fa67a34d3554e499dfc8a106d9149203b4eff3d9/crates/ffi/src/aiur/aggregate/shard_pipeline.rs#L25)
- Start with one proving job per domain; permit packing only when the combined
  live data and scratch fit. More simultaneous jobs can improve throughput while
  worsening each job and the tail. Do not make six-wide execution a universal
  default from one machine's results.
- Check affinity and memory-policy syscall results. The reviewed NUMA helper
  discards these return values; a port should report failure and take an explicit
  fallback, not claim successful isolation. [Pinning calls](https://github.com/argumentcomputer/ix/blob/fa67a34d3554e499dfc8a106d9149203b4eff3d9/crates/ffi/src/numa.rs#L256)
- Record THP, CPU/memory affinity, cgroup limits, swap and page faults with each
  comparison. Host-wide THP or NUMA-balancing changes belong in an approved box
  setup procedure, not an implicit side effect of proving.

The required single-batch dependency chain is:

```text
execute worker records
  -> settle deferred multiplicities and worker-entry corrections
  -> commit all trace shards (parallel, bounded)
  -> freeze ordered headers/messages and derive the batch challenges
  -> finish shard proofs (parallel, bounded)
  -> range leaves as proofs arrive -> joins as children arrive -> final root
```

Do not commit a record while other workers can still change its multiplicities.
For regeneration, each shard must reproduce its original header. Parallelizing
either pass must preserve this check and the shared transcript barrier.

Bounding the number of executing workers does not bound completed records waiting
at that barrier. Whole-Mathlib residency therefore needs an explicit retention
strategy: compact storage plus, where necessary, spill/reload or deterministic
re-execution. Retaining every shard's first-pass data and regenerating it trade
memory against work; neither makes the original records disappear automatically.
A record can be released only when all consumers that need it are finished.

### 2.4 Do not carry over environment-folding overhead by default

Direct joins are useful when combining independent environment claims: they
avoid an unnecessary wrap layer. They are not a reason to introduce multiple
CheckEnv claims into a single distributed execution. Trace ranges still require
recursive proof verification, but not frontier unions or assumption discharge
between workers. Compare total verified child bytes and proof-node counts, not
just the number of top-level claims.

## 3. B1: reusable SIMD quotient buffers

### 3.1 The allocation site is real and is in multi-stark

At the pinned dependency, `quotient_values_inner` is called once per SIMD packet.
It constructs new packed current/next-row vectors for stage 1, stage 2 and
optional preprocessing; a new graph sweep vector; and a new vector of user
constraint results, subsequently extended by lookup constraints.
[Packet evaluator](https://github.com/argumentcomputer/multi-stark/blob/2042565be1939cf2bef4b0d4d47ba3354473c5bf/src/prover.rs#L1107)

The graph evaluator already accepts a caller-owned vector. It clears its length,
reserves capacity and overwrites the evaluated nodes. Creating the vector afresh
at every call defeats that reuse. The degree-two lookup path already uses
stack arrays internally and appends into the supplied result vector; rewriting
its arithmetic is not necessary for this optimization.
[Graph sweep](https://github.com/argumentcomputer/multi-stark/blob/2042565be1939cf2bef4b0d4d47ba3354473c5bf/src/eval.rs#L54),
[Lookup evaluator](https://github.com/argumentcomputer/multi-stark/blob/2042565be1939cf2bef4b0d4d47ba3354473c5bf/src/lookup.rs#L184)

### 3.2 Recommended implementation

Use a scratch object with buffers for the three packed row windows, graph-node
values and complete constraint results. Allocate it per coarse work chunk or
explicit lane worker, then reuse it for many consecutive packets. In the serial
build, allocate once outside the packet loop. A Rayon initializer is per job,
not a guarantee of exactly one object per OS thread; budget and describe it
accordingly.

First change the graph/results buffers, which need no matrix API revision:
retain the sweep vector; clear the result vector; extend it with graph roots in
their existing order; append lookup constraints; perform the unchanged fold.
Reserve the full `constraint_count`, not only the user-root count.

Then add a fill-into-buffer row-packing path. Merely copying the result of
`vertically_packed_row_pair` into a reusable vector leaves its allocation in
place. Preserve the existing specialized matrix-view behavior and dense packing
fast paths, including cyclic row selection. A generic replacement that avoids
allocation but adds expensive row access can lose the intended benefit.
[Dense row-pair packing](https://github.com/Plonky3/Plonky3/blob/3152b14a89067c83775a8076cc262ffc48a1fd7c/matrix/src/dense.rs#L551),
[Matrix API contract](https://github.com/Plonky3/Plonky3/blob/3152b14a89067c83775a8076cc262ffc48a1fd7c/matrix/src/lib.rs#L386)

Prefer disjoint output chunks with ordered stores over collecting a separate
output vector per packet. Do not replace per-packet allocation with a shared
mutex-protected buffer, unbounded thread-local retained capacities, or scratch
allocation for every packet in advance. Account for scratch across all admitted
provers, not just one Rayon pool.

### 3.3 Invariants and expected benefit

This should be a storage-lifetime optimization only:

- Preserve current/next row order, cyclic indexing, SIMD lane order and domains
  smaller than the packing width.
- Overwrite every graph value that is read; clear constraint results before
  appending. Do not let a previous packet or circuit leak into the next one.
- Preserve user-root then lookup-constraint ordering, reversed alpha weights,
  extension-coordinate layout and selector normalization.
- Keep transcript observations, polynomial domains, commitments and serialization
  unchanged. With deterministic inputs/configuration, quotient values should be
  exactly equal; deterministic end-to-end proof bytes are a useful stronger gate.
- Keep scalar/non-parallel and CPU fallback behavior. Successful accelerated
  quotient paths bypass this loop, so this is not a claimed CUDA-kernel speedup.
  [Accelerator dispatch](https://github.com/argumentcomputer/multi-stark/blob/2042565be1939cf2bef4b0d4d47ba3354473c5bf/src/prover.rs#L665)

The previously cited 21.5-second quotient span is not an allocation-only timing
and was not reproduced here. Quotient processing also includes transforms and
commitment work. If allocation/avoidable buffer management occupies fraction
`f` of that span, eliminating it completely saves at most `21.5 * f` seconds
under a fixed-work additive model; actual reuse still performs the data fills
and arithmetic. No numerical speedup is established by this review.

Implement this upstream in multi-stark (and the matrix API if necessary), then
update ix's dependency pin. Do not patch a Cargo checkout as the deliverable.

## 4. C1: PRs 624 and 625 belong together

### 4.1 What 624 changes

Delayed let inference retains checked types and values with their defining
environment/depth, materializing expressions only when required. It avoids
repeatedly substituting through the remaining term. Ordinary reduction and
definitional equality still receive ordinary expressions. This is checked
kernel work, not a Rust-only memo-cache shortcut.
[Let-local inference](https://github.com/argumentcomputer/ix/blob/849d2acf21753743a0c6067bcba1fccdabbe20df/Ix/IxVM/Kernel/Infer.lean#L144)

Multiplication-row construction changes from repeatedly appending to a growing
limb list to constructing the result with cons. That removes quadratic prefix
copying and the irrelevant output prefix from the memo key. It does not make
general multi-limb multiplication linear: the improvement is to construction of
each product row. Carry relations and exact limb-list representation still
matter, including empty inputs and trailing zero limbs.
[Multiplication change](https://github.com/argumentcomputer/ix/blob/849d2acf21753743a0c6067bcba1fccdabbe20df/Ix/IxVM/Kernel/Klimbs.lean#L459)

These optimizations reduce work before trace planning, so any reduced rows can
help execution, record residency and proving. They do not depend on env sharding.
However, added helpers and changed grouping can increase committed width even
when selected query counts fall. Adopt the source, group-table cleanup and
regenerated executor consistently; do not copy only the generated Rust diff.

The PR reports complete ISLB checking, but its three focused FLT timings used
subject-only diagnostics with hashing/dependency checks disabled. Those timings
are not full FLT validation. Its broader FFT pins include both improvements and
regressions. [PR 624 validation boundaries](https://github.com/argumentcomputer/ix/pull/624)

The public seven-case pipeline benchmark is approximately flat (about -1.1% to
+1.3% total time), while base proof sizes rise around 1.6–1.8%. Treat this as a
targeted pathological-workload improvement, not an established whole-Mathlib
throughput gain. [624 benchmark](https://github.com/argumentcomputer/ix/pull/624#issuecomment-5612600838)

### 4.2 What 625 adds

PR 625 adds regression fixtures, not another production optimization:

| Fixture | Isolates | Reported FFT cost, old -> fixed |
| --- | --- | ---: |
| `IxVMPerf.let_continuations` | 64 interleaved let/application/lambda continuations | 374,093,264 -> 166,319,792 (-55.54%) |
| `IxVMPerf.mul_row` | A full U64 limb multiplied by 512 varied limbs | 1,051,404,589 -> 425,316,349 (-59.55%) |

Operands and the expected multiplication result are generated during elaboration,
so the checked theorem contains literals. Varied limbs avoid memoization hiding
the old copying behavior. These tests use full hashing/dependency traversal and
the existing native/bytecode parity harness. The quoted comparisons revert one
optimization at a time with the other fix and grouping unchanged.
[Fixture source](https://github.com/argumentcomputer/ix/blob/173c1b5e20c276eb68e1dcb45fb52dc7de2bb63e/Tests/Ix/IxVM.lean#L111),
[PR 625 measurements](https://github.com/argumentcomputer/ix/pull/625)

Use both fixtures when integrating 624, alongside ordinary controls. Exact FFT
pins expose changes in modeled work; they are not wall-time or soundness proofs.
Also retain negative/context-sensitive cases: capture under nested binders,
dependent applications, lets with invalid value types, and the same expression
under different local environments. Repinning must follow an explained change,
not mask one.

The inspected ix-work snapshot still has the old multiplication-row signature
and lacks the new let-inference helper and performance fixtures. The upstream
merge status therefore does not mean this worktree already includes them.

## 5. PR 621: selective adoption and integration hazards

### 5.1 D1: native setup and completion-driven scheduling

The useful setup pattern is one Rust-side pass that checks every constant's
content address and decodes its complete body while assigning ownership.
Mutual-block projection wrappers are assigned to the underlying block. Indexed
collection preserves deterministic ownership and error ordering. An independent,
temporary setup pool prevents a low execution-worker limit from serializing
startup; it is dropped before the execution pool is used.
[Native preparation](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/ffi/src/aiur/check.rs#L35)

For a single-claim driver, retain these validation properties without treating a
worker partition as a separately proved environment. A selected workload still
must not certify declarations it skipped. File-backed FFI remains an IO boundary;
do not turn a path read into an apparently pure memoizable operation.

The completion dispatcher is also a useful template: coordination happens outside
Rayon; running attempts plus pending completions are bounded; split children can
start without waiting for an unrelated slow peer; errors drain launched work.
[Completion dispatcher](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/ffi/src/aiur/admission/dispatch.rs#L17)

Important adaptation: that dispatcher assumes execution records are dropped
before work returns. Trace proving retains records or derived commitment data
after execution. Transfer the memory charge with that data and release it only
after its final consumer, not when the execution completion arrives. Copying
the dispatcher's permit lifetime unchanged would under-account retained data.

PR 621 separates local-record exhaustion, shared-budget pressure and semantic
failure. Local exhaustion can refine a block partition; shared pressure drains
and retries the same claim with a bounded retry count. Preserve these distinctions
when adapting worker execution, but do not copy its env-claim splitting as the
trace architecture. A failed or interrupted record is not a proof-ready record.
[Refinement policy](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/ffi/src/aiur/check/refine.rs#L134)

### 5.2 D2: compact records, hashes and multiplicities

Per-column byte/u32/field storage is selected from actual canonical values,
with lossless widening. Reused canonical key hashes reduce repeated hashing;
hash-table lookup still checks exact key equality. Owned hash/key metadata may
survive recursive calls, but a borrowed bucket cannot survive possible rehash.
These are useful storage candidates independent of the arithmetic changes.
[Packed storage](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/aiur/src/querymap/storage.rs#L139),
[Query lookup and hash reuse](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/aiur/src/querymap.rs#L321)

Reserve growth before touching new storage, including simultaneous old/new
segments and hash tables during widening/rehash. Release credits after dropping
the corresponding storage. These cooperative limits are not hard process-RSS
limits: witness buffers, stacks, allocator overhead, mappings and other live
objects require their own allowance and an independent OS cap.
[Growth accounting](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/aiur/src/querymap.rs#L482),
[Credit release](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/aiur/src/querymap.rs#L579)

Three concrete compatibility requirements for ix-work:

1. PR 621 reconstructs memory outputs from the insertion index and asserts that
   stored outputs equal that index. Distributed execution instead uses
   `pointer_base + index`. Store/propagate the namespace base in the compact
   representation and preserve load-index subtraction and namespace bounds.
   Porting zero-based implicit outputs literally would break nonzero workers.
   [Zero-based assumption](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/aiur/src/querymap.rs#L473)
2. Local `QueryRecord::absorb_deferred` adds arbitrary deferred counts through a
   mutable field reference, and worker-entry corrections subtract registrations.
   Compact counters need equivalent fallible add/set/subtract operations with
   lossless promotion and Goldilocks arithmetic, not just an increment API.
   Propagate failures through deferred calls, final settlement, hint promotion,
   the interpreter and regenerated executors. Do not truncate or saturate counts.
   [Compact counter implementation](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/aiur/src/querymap/multiplicity.rs#L87)
3. Adapt shard row indexing, grouped member selection and regeneration to packed
   query views. Preserve insertion order, selected row IDs, selector offsets,
   original function-channel identities and exact lookup/main traces. Avoid
   recreating decoded per-row allocations in the witness builder.
   [Grouped packed trace construction](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/crates/aiur/src/trace.rs#L104)

Keep compact multiplicities opt-in until end-to-end evidence supports enabling
them. Lower retained bytes alone does not establish faster memo access or proving.

### 5.3 Arithmetic/substitution overlap is not additive

PR 621 also changes multiplication and substitution. Its linear row construction
overlaps 624; its later fused multiplication is additional work, not a second
copy of the same gain. Integrate each transformation once. Prefer 624 plus 625
as the small, already-merged starting point; consider further fusion separately.

Trailing substitution-key projection must preserve the original substitution
window length and binder depth: variables above the window still shift by the
original number of removed binders. It is not permission to remove arbitrary
interior arguments or share results under different contexts. Keep projected
memo keys in checked Aiur code rather than an invisible host-only equivalence.
[Projection implementation](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/Ix/IxVM/Kernel/Subst.lean#L526)

### 5.4 Public regression evidence changes the adoption recommendation

The fresh post-rebase benchmark comment compares head `3e7586a` against base
`4c91254`. Its seven ordinary cases report:

- IxVM execution roughly 38–49% slower for several larger cases.
- Total pipeline time roughly 5–20% slower across the seven cases.
- Standalone recursive-verifier proofs (the benchmark's FRI-verifier-on-FRI
  section) around 4.00–4.01 MiB instead of about 2.21 MiB, approximately 80–82%
  larger, despite near-flat modeled FFT costs.
- Native recursive-proof verification also slower in that report.

This is not a matched whole-Mathlib or whole-FLT result and does not isolate the
responsible subchange. It is nevertheless direct evidence against a blanket
performance recommendation for the combined branch. These are not measured
`ix_aggr` range nodes, but if the same proof-size increase propagates into them,
it would matter at every tree level. Require a separate explanation and
grouping/active-width comparison before adopting that part.
[621 post-rebase benchmark](https://github.com/argumentcomputer/ix/pull/621#issuecomment-5607232117)

The PR's small pre-rebase wins and its rebased FFT-pin totals are different
experiments. Its full FLT execution was still reported in progress on a frozen
pre-rebase binary, with no STARK generation. Do not present it as a completed FLT
proof or as validation of the current grouped prover. [621 scope and rollout status](https://github.com/argumentcomputer/ix/pull/621)

## 6. Range-sum WIP: retain the algebra, finish the systems work

The reviewed ix-work leaf verifies shards against a digest-bound preamble; joins
require a common digest and adjacent ranges and add checked residuals; the root
requires complete coverage, closure policy, balance and the original single
claim. No new soundness hole was identified in that composition during the
earlier static review. That is not a formal soundness certification.

Snapshot locators below refer to `/home/ubuntu/ix-work`, not the document
workspace. Recheck them against subsequent WIP edits:

| Finding | Local source locator | Required direction |
| --- | --- | --- |
| Nested `--jobs` | `crates/ffi/src/aiur/aggregate.rs::prove_range_level`, `run_scheduler`, context `wrap_budget`/`range_jobs` | One admission system; up to J outer trees must not each launch J nodes with a B/J allowance |
| Grouped estimate gate | `crates/aiur/src/synthesis.rs::raw_of`, `prove_ixvm_within_budget` | A1 applies before the range prover's trace-shard decision |
| Batched/level barriers | `aggregate.rs::prove_range_tree` | Queue individual ready nodes; start a parent once both children finish |
| Only final slot root cached | `aggregate.rs::prove_range_tree` | Persist and verify individual range-node checkpoints |
| Fixed shard-count ranges | `aggregate.rs::prove_range_tree` | Use contiguous cost/byte-aware ranges subject to execution and proving budgets |
| Full preamble per leaf | `Ix/Aggr/Circuit.lean::aggr_load_preamble` | Keep as an explicit compatibility phase; plan compact authentication when needed |
| Existing aggregation function groups | `Ix/Aggr/FunctionGroups.lean` | Measure range-specific active widths before assuming 1–3 MB internal proofs |
| Direct joins bypass range wrapping for raw multi-leaf inputs | `aggregate.rs::prove_slot` | Define flag precedence or normalize oversized children before their direct join |

For a single whole-env batch, the nested-tree multiplier is absent, but the
incorrect peak gate and missing shared residency accounting still matter.
Individual node cache keys should include the authenticated batch identity,
range endpoints and verifier/protocol identity. Verify the cached statement and
proof before reuse; a path name or matching range alone is not authentication.

With L range leaves, the present tree builds L leaf proofs, L-1 joins and one
final root wrapper: 2L proofs. The benefit is bounded leaf verification and
simpler claims, not zero Stage 2 work. A later optimization could fuse the final
join/root, but that is lower priority than accurate resource accounting.

Every leaf currently processes the whole preamble. If its size is P, L leaves
repeat at least O(L * P) scan/hash/parse work. Making leaf ranges smaller does
not shrink that per-leaf component. A Merkle-committed transcript context can
improve scaling, but requires coordinated prover, native verifier and in-circuit
changes with all headers/messages/policy facts authenticated. Do not substitute
new challenges only in the wrapper. The leaf/join/root algebra can survive that
revision; the context authentication and leaf inputs cannot simply be assumed
unchanged.

Likewise, a smaller range statement does not itself prove that recursive STARKs
will be 1–3 MB. Active verifier circuits, mixed function-group widths, trace
sharding of the recursive execution and proof parameters determine the result.
Try range-specific grouping before concluding that a separate pruned recursion
system is necessary.

Base trace planning and recursive range planning are separate levers. Size hot
circuit row slices to the available budget instead of blindly repeating every
hot circuit in every shard. Track both padded committed cells and the sum of
active committed widths across shards: fewer rows or a lower per-shard RAM peak
can still produce more bytes for recursion to verify. Choosing a larger range
leaf does not remove that base-proof duplication.

## 7. M1: verification and performance accounting

The cluster run's five-second root-verification figure must not be used as an
established warm native-verifier latency. Its aggregate command loads/audits the
environment, builds the backends, loads/decodes the proof and then verifies it.
The code has separate audit, setup and proof-check timers; the proof-check timer
surrounds `backend.system.verify` after setup and decoding. The published PR
does not supply the raw root log needed to divide those five seconds exactly.
[Verification timer](https://github.com/argumentcomputer/ix/blob/fa67a34d3554e499dfc8a106d9149203b4eff3d9/Ix/Cli/VerifyCmd.lean#L196),
[Audit/setup timers](https://github.com/argumentcomputer/ix/blob/fa67a34d3554e499dfc8a106d9149203b4eff3d9/Ix/Cli/VerifyCmd.lean#L330)

There is supporting, but different, evidence: 624's published benchmark lists
native checks of roughly 4.5–5.15 MiB IxVM proofs at approximately 24.5–29.9 ms.
That supports the plausibility of subsecond native checks; it is not a
measurement of the Mathlib aggregate root. If the root's proof-only timer says
5,000 ms, setup cannot explain it and constraint/PCS verification needs separate
investigation. [624 verification measurements](https://github.com/argumentcomputer/ix/pull/624#issuecomment-5612600838)

Another useful 621 change is explicit timing of IO execution. When an FFI path
changes from a pure-looking thunk to an IO action, the benchmark must time
running the action, not constructing it. Preserve the `timedIO` discipline and
check equivalent measurement boundaries when comparing old and new binaries;
do not attribute a timing change to storage or arithmetic without that check.
[Benchmark timing change](https://github.com/argumentcomputer/ix/blob/3e7586a7adb0c6f3cd3ff5854da832701288ec90/Benchmarks/Typecheck.lean#L381)

Report these separately in future comparisons:

| Layer | Measurements |
| --- | --- |
| Input/setup | File load, coverage/ownership audit, compilation/backend/VK setup, decode |
| Execution | Wall time, CPU work, unique/duplicate queries, records and memo behavior |
| Base proving | Commitment pass, regeneration, second pass, quotient subphases, shard count |
| Recursion | Leaf/join/root counts, input bytes verified at each layer, active width, output bytes |
| Native verification | Warm proof-only latency, separately from end-to-end command wall time |
| Resources | Accounted storage, process RSS, cgroup charge, per-node residency, lookahead and scratch |

Model whole-run wall time as a dependency schedule, not a sum of overlapping
spans or a product of unrelated benchmark speedups. Keep work/box-hours separate
from elapsed time. Keep execution-only success, complete proof generation and
final claim-bound verification as distinct outcomes.

## 8. Implementation sequence and acceptance gates

These are recommendations for subsequent work; none was executed for this doc.

1. Fix A1 and unify memory admission. Resolve range/outer job accounting before
   increasing concurrency. Record the exact circuit/grouping identity behind
   every estimate and cached artifact.
2. Implement B1 as an isolated multi-stark change. Compare exact quotient values
   on tiny/wrapping domains, scalar/SIMD and parallel/non-parallel paths. For
   deterministic configurations, compare proof bytes as well as verification.
   Measure allocations, packet-loop time, full quotient time and whole prove
   time separately; retain the existing arithmetic and transcript.
3. Integrate 624 and 625 together, regenerate from the Lean source and explain
   cost-pin changes. Compare ordinary workloads alongside the targeted fixtures;
   preserve negative cases and native/interpreted parity. These changes affect
   circuit/VK identity, so old proof caches must not be treated as compatible.
4. Add admitted NUMA-local batch-pass workers, completion-driven range scheduling
   and per-node checkpoints. Preserve the preamble barrier and regenerated-header
   equality. Bind records and lookahead memory to their actual lifetimes.
5. Port 621's native preparation, credits and compact representations in separable
   steps. Resolve namespace-aware implicit pointers and deferred-count mutation
   before enabling compact storage in distributed execution. Require exact
   grouped/sharded witness parity for storage-only changes; investigate the
   published ordinary-workload and recursive-proof-size regressions.
6. Once widths and costs are known, tune range cuts and function groups. Introduce
   compact preamble authentication if repeated context work becomes material.

For storage and scheduling changes, future acceptance should include malformed
inputs, widening/rehash pressure, shared/local exhaustion, cleanup after failure,
bounded retry, corrupt checkpoints and exact final claim coverage. For kernel
changes, semantic parity is necessary but query-count identity is not expected.
For scratch reuse, arithmetic/output identity is expected and no re-pinning of
kernel FFT costs should be necessary.

The intended result is not a hybrid that permanently pays both worker locality
costs and environment-claim folding. It is one claim, bounded and correctly
accounted worker/prover state, parallel batch passes, and a resumable range tree
whose cost is evaluated from actual proof bytes and circuit work.
