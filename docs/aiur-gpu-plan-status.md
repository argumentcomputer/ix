# Trace-sharded Aiur on GPU: measured ladder and status

For the current code pins, queue22 evidence, and Mathlib run sequence, read
[the pre-Mathlib handoff](aiur-gpu-mathlib-handoff.md). This page preserves the
earlier measurement ladder as well as the later results.

2026-09-11. Bases: ix `sb/aiur-trace-sharding-gpu` (on `sb/aiur-distributed-execution`
e3a29720) and multi-stark `sb/trace-sharding-gpu` (on `sb/trace-sharding` 9322ec0,
fork at `~/multi-stark-ts`; ix `Cargo.toml` carries an uncommitted `[patch]` to it).
Box: 32 cores, 249 GiB, RTX PRO 6000 (96 GB), THP `always` from 23:13 on 2026-09-10.
Inputs, logs and scripts: `~/benchdata/trace-shards-gpu/`. The recommendations this
follows are `docs/aiur-gpu-performance-recommendations.md`; the earlier plan is
`docs/aiur-trace-sharding-gpu-plan.md`.

## Init as one claim, single record, 1.5e9 cells, cap 2^24, Regenerate

| run | K | STARK rounds | whole `ix prove` | host peak | VRAM peak | faults / sys |
|---|---|---:|---:|---:|---:|---|
| CPU binary (this box, same planner) | 36 | 1514 s | 31:38 | 164 GiB | — | 679 M / 1891 s |
| GPU baseline (design branch, THP madvise) | 40 | 625 s | 16:45 | 112 GiB | 66.5 GB | 402 M / 1014 s |
| v2: pool retention, managed slab, witness pipeline, trace-only lookups, THP always | 36 | 326 s | 11:32 | 109 GiB | 66.6 GB | 0.9 M / 335 s |
| v3: + staged pinned upload, pipeline on the two-call API, new base | 35 | 181 s | 9:11 | 107 GiB | 66.7 GB | 0.9 M / 144 s |

Per-shard means, v3: witness 1.3 s (hidden behind the GPU), stage-1 commit 1.4 s
(×2), lookup 0.7 s, quotient 0.7 s, FRI 0.6 s. Round one 1.5 s per shard, round
two 3.4 s. Execution (single-threaded, 361 s) is 66 % of the wall.

The 64-core CPU box's same-shape run on the branch (36 shards, 1.8e9 cells):
455 + 1372 s of STARK, 36:45 wall. v3 is ~10× on the STARK rounds against it and
~8.4× against this box's CPU binary; end to end it is 4× / 3.4× because execution
is untouched.

What each step bought (nsys, `stark/*` spans):

- THP `always` and pool retention: page faults 402 M → 0.9 M; system time 1014 →
  335 s; lookup/quotient/FRI halved (their buffers stopped being remapped).
- Managed control-block slab: removes one synchronizing `cudaMallocManaged`
  per LDE (was 1.1 s each under 16-way concurrency).
- Staged pinned upload: `cudaHostRegister` was 1.9 s per large trace even with
  huge pages, plus 0.6 s to unregister; stage-1 commit 3.4 → 1.4 s.
- Witness pipeline: witness build (1.3–2.4 s per shard) no longer on the
  critical path.

## Init as one claim, distributed: 8 ordered chunks, `--cells 1.5e9`, v3

| quantity | result |
|---|---|
| wall | 16:42 (single record: 9:11) |
| host peak / VRAM peak | 62.5 GiB / 66.7 GB |
| shards / proof | 56 (10/8/7/7/7/6/6/5) / 140.7 MB, `ix verify` ok |
| round-one executions (all 8 at once) | 44–82 s each |
| round-two re-executions (one prefetched ahead) | 44–85 s each, 491 s in sum |

The GPU proves a record's shards in ~10–25 s and then waits for the next
re-execution: with prefetch depth 1, round two is bounded by the sum of the
re-executions. Records total 118 GB, so on this box keeping every record
across the barrier (recommendation 6) removes round two's execution
entirely; that is the next run.

### Where the distributed time goes (v5, instrumented, 8 chunks, records kept)

| phase | time |
|---|---:|
| round one (`stark/batch_round_one`) | 410 s, of which 56 commits = 78 s |
| round-one executions, strictly serial (prefetch depth 1) | done at +84, +155, +218, +281, +340, +391, +441, +486 s |
| round two (`stark/batch_round_two`, no re-execution) | 194 s = 56 × 3.4 s |
| per-shard means | witness 1.1 s, stage-1 commit 1.4 s, lookup 0.7, quotient 0.7, FRI 0.6 |

The per-shard costs equal the single-record run's, so the distributed path has
no prover penalty; the 21 extra shards from chunking cost ~100 s. Round one is
execution-bound because ordered chunks are singleton caller groups and the
driver executed one worker ahead. `--exec-ahead N` (v6) keeps N executions in
flight; with N = 8 on Init round one should be ~85 s of execution plus the
commits. Keeping records (`--keep-records`) removed round two's 491 s of
re-execution here; for Mathlib the equivalent is a byte-budgeted cache plus
out-of-order round two (each proof carries its shard index), not keeping
everything.

### Execution window (v6, `--exec-ahead N`)

| run | wall | host peak | round one | round two |
|---|---:|---:|---:|---:|
| 8 chunks, records kept, window 1 (v5) | 11:34 | 185 GiB | 410 s | 194 s |
| 8 chunks, records kept, window 8 (v6) | 7:16 | 189 GiB | 152 s | 195 s |
| single record (v3), for reference | 9:11 | 107 GiB | 60 s | 121 s |

With the window, workers 1–7 executed concurrently but only after worker 0's
83 s solo run (the first caller group executes before the batch opens the
window); v7 opens the window at startup. A 4-wide window without kept
records exposed a driver bug (round-two executions started during round one
were settled early and respawned; worker 0 ran three times); v7 guards a held
record against re-execution.

| 8 chunks, records kept, window 8, window open at start (v7) | 6:19 | 187 GiB | 87 s | 195 s |
| 8 chunks, no records kept, window 4 (v7) | 9:42 | 175 GiB | — | GPU < 10 % busy: starved on re-execution |

### The budget-driven pipeline (v8)

The interim flags (`--exec-ahead`, `--keep-records`, `--no-prefetch`) are
replaced by one rule: records may occupy host memory up to `--max-ram`
less the prover's working set (two shard witnesses at the cell budget plus
upload staging). The driver executes ahead in commit order while that
budget has room (charging a record's execution-RSS estimate until it is
measured, then the largest measured record), hands records to the prover
in order, retains each after its first round while room lasts, and evicts
the resident record whose next use is furthest when an execution needs the
space. An execution the prover needs is never refused, so the budget bounds
what runs ahead rather than guaranteeing a peak; a record that alone
exceeds it is reported and the fix is smaller chunks. Round two proves in
commit order; a slow chunk can hold up later ready ones, accepted for the
simpler scheduler.

Measured (v8, first cut of the pipeline; 8 ordered chunks, 1.5e9 cells):

| run | wall | host peak | GPU busy | round-two re-executions |
|---|---:|---:|---:|---:|
| `--max-ram 200` (record budget 177 GiB) | 7:11 | 186 GiB | 221 s of 412 s | 0 |
| `--max-ram 100` (record budget 77 GiB) | 9:28 | — | 236 s of 568 s | 8 (all evicted) |

Both verified. The idle gaps were all waits for executions: worker 0 ran
alone for 81 s before the window opened, and the execution-RSS estimate
(~30 GB per chunk against 10–23 GB measured) kept charging in-flight
executions after records had been measured, which at 100 GiB evicted every
retained record. v9 charges the largest measured record once anything is
measured and opens the window before worker 0.

v9 (charge measured sizes once anything is measured; window open before
worker 0): `--max-ram 200` 6:18 (the keep-everything floor), `--max-ram
100` 8:48 with the head records still evicted because 3 in-flight charges
of 23 GB fill a 77 GiB record budget; both verified.

### Admission without a predictor (v10, v11)

The execution-RSS model is gone from this path. What replaces it is
weaker than "model-free" and should be read precisely: the size charged for
a record is its accounted content (`record_retained_bytes`: field elements
and query entries, plus IO), not allocator capacity or execution RSS, and it
is known only after the record exists. Sources, in order: the manifest's
measured-peaks section when an `ix prove --distributed --exec-only
--out-ixes` pass wrote it (optional, a diagnostic aid, not a requirement);
the largest record this run has measured; nothing, in which case only the
`--exec-jobs` ceiling (default: one per core) bounds what runs ahead. The
budget therefore limits speculative admission and retention; an execution
the prover needs is never refused, and nothing stops a running execution
from growing. Overruns are handled outside the executor, not by accounting inside it:
the driver also refuses to run an execution ahead when the process's actual
resident size plus the next record's charge exceeds `--max-ram`, the run
itself goes under a cgroup cap so an overrun is a clean kill rather than a
box OOM, and the recipe retries a killed run with `--exec-jobs` halved:

```
systemd-run --scope -p MemoryMax=230G -p MemoryHigh=220G -- \
  ix prove --ixe init.ixe --ixes init-ordered-8.ixes --distributed \
    --cells 1500000000 --max-ram 200 --exec-jobs 8 --no-index
# exit 137 (killed by the cap): rerun with --exec-jobs 4, then 2, then 1
```

Measured (v10, from a measured manifest): `--max-ram 200` 6:20, all eight
executions concurrent from t = 0, verified. The exec-only pre-flight cost
4:13 because it also scheduled round-two executions (fixed in v11); v11
reports cold proving (no pre-flight) as the primary result.

### Cold proving with the final driver (v11)

| run | wall | host peak | GPU busy | round-two re-executions |
|---|---:|---:|---:|---:|
| `--max-ram 200`, cold | 6:20 | 178 GiB sampled (186 `time -v`) | 223 s of 362 s | 0 |
| `--max-ram 100`, cold | 6:18 | 176 GiB sampled (189 `time -v`) | 228 s of 360 s | 0 |

Both verified (byte-identical to every earlier Init batch proof). The only
idle gap is the first ~95 s, the concurrent first-round executions. Read
the second row carefully: `--max-ram 100` was exceeded by ~80 GiB, because
on a cold start all eight workers are admitted at once (`--exec-jobs`
defaults to the core count) before any record is measured, so the budget
had nothing left to gate and the retained records were what fit the box,
not the flag. `--exec-jobs` bounds the first wave, the cgroup cap is the
hard limit, and the recipe halves `--exec-jobs` on a kill. What the flag
does once sizes are known is below (the budget trim): it releases the
over-budget part of that first wave instead of carrying it through the
barrier. For Mathlib set `--exec-jobs` from the chunk sizes the manifest
was cut for, and run under the cap.

## Stage 2 on the device (range tree over the 56-shard batch)

`ix aggregate --range 12 --trace-shards --jobs 1 --max-ram 100`, each node
trace-sharded to 1.5e9 cells (`AIUR_TRACE_SHARD_MAX_CELLS`), one node at a
time. Root 8.05 MB, `ix verify --aggregate` 1.2 s, 56,621 constants
certified.

| node | wall | execution (CPU) | round one | round two | shards |
|---|---:|---:|---:|---:|---:|
| range leaf ×5 (12, 12, 12, 12, 8 shards) | 39–49 s | 15–19 s | 9–12 s | 15–18 s | 5–6 |
| join ×4 | 30–38 s | 12–15 s | 7–9 s | 11–14 s | 4–5 |
| root | 19 s | 7 s | 5 s | 7 s | 2 |
| tree | 372 s (6:16 wall) | 145 s | 92 s | 134 s | 46 |

Host peak 30 GiB (the CPU model's per-node projection of 63–74 GiB is
more than 2× high), VRAM peak 56 GB, GPU active 41 %: idle exactly during
each node's execution, since the aggregate scheduler has no lookahead. A
join verifying two proofs costs ~30 s against ~45 s for a leaf verifying
twelve, so the fixed floor per node (preamble replay, child verification,
the node's own pipeline start) is ~25 s and each shard verification
~1.5 s; floors are ~250 s of the 372 s. Fewer nodes is the lever: see the
`--range 28` / `--range 56` rows below. The same pipeline as Stage 1
(execute node k+1 while node k proves) would recover most of the 41 %
idle; the tree's parallel leaves buy nothing on one GPU.

The 6:16 above was measured at THP `madvise` (a reboot had reset it). With
THP `always`, under a 230 GiB user-scope cgroup cap:

| tree | nodes | wall | tree | host peak | root |
|---|---|---:|---:|---:|---:|
| `--range 12` | 5 leaves, 4 joins, root | 5:28 | 325 s | 31 GiB | 8.05 MB, verified |
| `--range 28` | 2 leaves (90, 98 s), join (56 s), root (24 s) | 4:32 | 269 s | 44 GiB | verified |
| `--range 56` | not a tree: width = shard count took the whole-wrap path; one 25-shard wrap, 40 MB | 3:16 | — | 62 GiB | not comparable |

| one leaf (56) + root, lookahead build | leaf executed 90 s (exposed), proven 190 s; root 54 s | 4:08 | 245 s | 62 GiB | 16.6 MB root, verified |

Fewer nodes wins up to the point where the pipeline has nothing to
overlap: one leaf leaves its whole execution exposed and its root grows
(16.6 MB against 8 MB). The range is therefore not a per-machine constant:
`--range 0` with `--trace-shards` derives the width as ⌈shards / 2·jobs⌉,
two leaves per node slot (one slot per GPU), so a slot always executes its
next leaf while proving one and each leaf is as large as that allows; a
leaf over the slot budget fails its gate or the cgroup cap and the recipe
halves the width. On this box that is 28, the measured best. Node
execution is pipelined one node ahead of proving within each level
(`prove_range_level`).

| `--range 28`, lookahead | leaf executions 40 + 53 s, the second overlapped with the first leaf's proof | 3:46 | 223 s | 58 GiB | verified |

End to end on this box, Init as one claim: Stage 1 6:18 + Stage 2 3:46 =
10:04 to a verified root, against 47:40 (env shards) / 54:01 (trace
shards) on the 64-core CPU box. Stage 2's GPU was active ~45 % of its
wall: the first leaf's execution and the join/root dependencies remain
exposed; the next lever is executing the first leaf while Stage 1's last
shards prove, which needs the two commands to share one pipeline.

## Mathlib: the pointer namespace (reverted)

The first Mathlib distributed run (256 ordered chunks) failed in worker 0
because its width-3 memory table needed 238 M entries and the chunk
model's per-worker pointer namespace was 2^32 / 256: records proven in one
batch share one pointer space, and the kernel compares pointers as `u32`.
A kernel change gave every record a full 2^32 namespace (pointers ordered
within a namespace, +0.2 % queries, regenerated kernels). With env-shard
claims (below) every proof is one record at base 0, so that change was
reverted; what stays is the guard: `Store` fails when a memory table
reaches 2^32 entries, in the interpreter and in generated code, which is
the bound the kernel's `u32` comparison rests on. The chunk model keeps
its earlier per-worker limit.

## Blake3 and LDE kernel work (fork commits ff3237c, f15a6c4)

Two multi-stark CUDA commits (single-chunk Blake3 rows hashed one thread
per message; wide NTTs fused at any height with fewer LDE memory passes)
measured end to end on Init in queue22, with both stages verified. Stage 1's
batch hash matches the namespace-kernel baseline. The older Stage 2
range-28 comparison used a different batch and ix binary, and its root hash
differs; that row is a historical comparison rather than an isolated kernel
A/B. Exact logs and fingerprints are in the
[pre-Mathlib handoff](aiur-gpu-mathlib-handoff.md).

| | before (namespace kernel) | after |
|---|---|---|
| Stage 1, distributed 8 chunks, wall | 6:26 | **5:47** |
| stage-1 commit per shard (mean) | 1.57 s | 1.32 s |
| round two per shard (mean) | 3.58 s | 3.09 s |
| Stage 1 GPU util-seconds | 194 | 149 |
| Stage 1 peak host RSS | 177 GiB | 174 GiB |
| Stage 2, `--range 0` (= 28), wall | 3:46 | **3:41** |
| Stage 2 range tree | 223 s | 218 s |
| Stage 2 GPU util-seconds | 91 | 74 |
| end to end to a verified root | 10:12 | **9:28** |

Stage 1 gains 10 % of wall from 16 % off the commit floor and 23 % less GPU
busy time; Stage 2 gains little because its wall is execution and
dependency bound (leaf executions 41 + 53 s, join 26 s), not kernel
bound. The cold first wave of executions (~80–90 s before the first shard
proves) is unchanged and is now the largest fixed cost in Stage 1.

### Review fixes before the Mathlib run

Five findings from the last review, all in place before Mathlib Stage 1
restarts:

- **Retained records are trimmed to the budget.** Measured on Init at
  `--max-ram 100` before the trim: the cold wave left 119 GB of records
  resident against a 77 GiB budget, nothing was ever released (eviction
  only served admission, and nothing needed admitting), no round-two
  execution ran, and the run peaked at 175 GiB, the same as at
  `--max-ram 200`. Now every fill trims what is retained to the budget,
  furthest next use first; the released records re-execute for round two.
  Measured (`--max-ram 100`, trim in place): peak 152 GiB after the cold
  wave, but 9:42, then 9:04 with the RSS gate removed, because a released
  first-round record is only regenerated on demand (`needs` treats an
  executed-then-released worker as needing nothing), one at a time on the
  critical path. Not fixed: the env-shard path below has no barrier and
  none of this machinery; the trim and gate removal are left uncommitted.
- **Retained records made room for required executions.** The driver
  refused to run an execution ahead when retained round-two records filled
  the budget, but a required execution ran regardless, on top of them.
  Now both paths release retained records (furthest next use first) until
  the charge fits the budget and the process's actual RSS beside
  `--max-ram`; only when nothing releasable remains does an execution ahead
  wait. Finished executions are harvested on every fill, so their slots and
  measured sizes are current when the next admission is decided.
- **Stage 2 default width scales.** `--range 0` derives
  `ceil(K / (2 · jobs))`; when a leaf at that width fails its slot-budget
  gate the width is halved and the level retried, so the default follows
  the machine's budget instead of failing on it. A requested `--range N`
  is left to the caller.
- **Device and host caps are separate.** With `AIUR_TRACE_SHARD_MAX_CELLS`
  set, every trace-sharded proof is planned to committed cells and the plan
  is then held to the host budget; before, a record whose whole-execution
  peak fit the host budget was proven as one shard, ignoring the device
  bound.
- **Omitted lookup witnesses fail closed** (row 3 above).
- **Impossible budgets fail before planning.** The planner's floor is the
  record plus the byte tables at full height, calibrated; a budget under it
  returns that floor without cutting a plan, and the halving search stops
  at twice the widest circuit's width instead of running the cell budget
  to zero.

## Env-shard claims on the GPU (2026-09-11, afternoon)

The user's question: are the chunk objects (one claim, many records,
barrier) worth it against env shards, which give independent claims and
claim-level resume? Measured on Init with the same binary and cell cap,
`ix prove --ixes M --trace-shards --retention regenerate --max-ram 200`
for Stage 1 and `ix aggregate --direct-joins --structural-above 0
--trace-shards --jobs 1 --max-ram 200` for Stage 2 (direct joins: the
first join verifies two raw claim proofs, so K claims cost K-1 joins and
no wrappers; each join is itself trace-sharded):

| Stage 1 | 8 chunks, one claim | 8 env shards (same partition) | 4 env shards, ordered | 4 env shards, min-cut |
|---|---|---|---|---|
| trace shards | 56 | 58 | 49 | **42** |
| records | 10–23 GB, all resident | 12–21 GB, one at a time | 21–34 GB | 20–24 GB |
| GPU util-seconds | 149 | 148 | 130 | **119** |
| STARK (rounds one + two) | | | 232 s | **195 s** |
| peak host RSS | 174 GiB | 51 GiB | 58 GiB | **53 GiB** |
| wall | 5:47 | 12:14 (serial) | 11:26 (serial) | 9:46 (serial) |

| Stage 2 | chunk range tree | 8 env shards | 4 ordered | 4 min-cut | 4 min-cut + `--wrap-root` |
|---|---|---|---|---|---|
| nodes | 2 leaves, join, root | 7 joins | 3 joins | 3 joins | 3 joins + 3 wraps |
| trace shards | | 43 | 26 | 24 | 24 + 6 |
| wall | 3:41 | 5:28 | 3:17 | **2:51** | 3:32 |
| root | 9.5 MB | 11.9 MB | 14.9 MB | 14.6 MB | **6.0 MB** |

Every run verified (composed verdict over the claims, then the root over
all 56621 constants). Findings:

- **The proof model costs nothing.** Eight env shards on the chunk run's
  own partition prove the same work (58 vs 56 shards, 148 vs 149 GPU
  seconds). The chunk model's worker-0 walk and deferred calls buy no
  proving time.
- **Min-cut beats the ordered layout for independent claims**: the
  largest record drops from 34 to 24 GB, trace shards from 49 to 42, and
  Stage 2 joins carry fewer cross-claim assumptions (2:51 vs 3:17). The
  ordered layout existed for the shared batch's commit order; independent
  claims carry their assumptions explicitly and do not need it.
- **More claims, more joins**: Stage 2 is K-1 serial joins at `--jobs 1`,
  so choose the env-shard count from execution memory and CPU parallelism
  (the reviewer's rule) and let trace shards cover the GPU.
- **Host memory is a third**: records are executed, proven and freed one
  claim at a time. Nothing on this path needs the budget driver, trim,
  eviction, RSS gate, or pointer namespaces.
- **The serial Stage 1 wall is a scheduling artifact**: `ix prove --ixes`
  executes shard k, proves k, executes k+1. STARK time for the min-cut
  four is 195 s; the rest is three executions run one after another.
  Executions run ahead (all four at t = 0, the GPU starting on claim 0 as
  its record lands) project Stage 1 to about 5:00, the chunk model's wall
  with a third of its memory and claim-level checkpoints. That loop is the
  next implementation step: execute up to `--exec-jobs` shards ahead on
  threads, prove in order, persist each proof and its index entry as it
  completes.
  Built (commit 851a06ef, `ix prove --ixes M --trace-shards --exec-jobs N`)
  and measured on the min-cut four: **5:04** (all four executions
  concurrent, landing at 95–109 s; the GPU then proves 52 + 50 + 48 + 45 s
  back to back), the same 42 shards, peak 128 GiB, verified. Init end to
  end: 5:04 + 3:32 = **8:36** to a single-STARK 6.0 MB root, against 9:28
  for the chunk pipeline.
- **`--wrap-root`** (shape 1, one `ix_aggr` child, statement passed
  through) wraps until the final proof is one trace shard: 7 → 3 → 2 → 1
  in 39 s, 14.6 → 6.0 MB. The first attempt exposed that a plan the
  planner chooses to retain across the barrier reads the host lookup
  witness on the CUDA backend; under trace-only lookups every plan now
  regenerates.

Decision: build the GPU pipeline on env-shard claims (min-cut manifest,
trace shards per claim, direct joins, root wraps). The chunk driver stays
on the branch as measured, not as the path forward.

## Mathlib Stage 1 on one GPU (2026-09-11 evening)

`ix shard mathlib.ixe --shards 128` (min-cut, 65 s), then
`ix prove --ixe mathlib.ixe --ixes mathlib-mincut-128.ixes --trace-shards
--retention regenerate --max-ram 200 --exec-jobs 4 --skip-proven` under the
230G cap:

| Mathlib Stage 1, 128 min-cut claims | |
|---|---|
| wall | **1:39:16** |
| trace shards | 1209 (9.4 per claim) |
| proof per claim | 43.8 s mean |
| execution per claim | 116.5 s mean, 282 s max (4 at a time) |
| record | 20.2 GB mean, 42.2 GB max |
| peak host RSS | 170 GiB |
| GPU | 57 % mean utilization, active 74 % of samples |

The prover was inside a proof 97.5 % of the time; the 40 % idle is inside
each proof (witness at the start of each round, round-two regeneration,
the barrier, host lookup construction), not between claims. Stalls on slow
shards (the loop took records in manifest order) totalled ~2.25 min; the
loop now takes whichever record is ready. The CPU production baseline on
r8i.48xl-metal (192 vCPU, 1.5 TB, 3 NUMA lanes): Stage 1 2:44 over 246
leaves, Stage 2 1:52 with direct joins, **4:36** end to end, 4.91 MB root
over 679,499 constants. Stage 2 of this Mathlib run was not proven; the
128 claim proofs are in the store and the shard-proof index.

### Stage 2 lookahead and ready-order Stage 1 (commit a2faf5e3)

The direct-join scheduler runs two lanes: `--exec-ahead` (default 1)
prepare workers — verification, advice, the `ix_aggr` execution planned
within the slot budget — beside `--jobs` provers, so a join executes
while the previous one proves; a queued record counts against the
lookahead, the prover lane is dispatched first, verify-only leaves have
their own allowance, nothing proves off the prover lane, and with trace
shards the static per-shape RAM weights gate nothing (they describe whole
CPU proofs and would keep every slot alone). Init, min-cut four: Stage 1
5:04 → 4:53 (ready order), Stage 2 with wraps 3:32 → 3:05, same 6.0 MB
root; on a four-leaf tree the root join and the wraps cannot overlap, so
the Mathlib tree (127 joins, wide bottom levels) is where the lookahead
pays.

### `ix verify --ixes` composed verdict, natively and in parallel (commit 3ba6a656)

The Lean composed verdict rebuilt each shard claim on one core (~15 s per
Mathlib shard; the 128-claim check was killed after 35 min). Ported from
`sb/cluster` (eacdfe24): the native Stage 2 entry's `verify_only` mode
reconstructs every claim in Rust, binds each proof by claim digest and
verifies all proofs in parallel. Mathlib, 128 claims: claims 1.6 s,
verification 1.0 s, 59 s wall (env load). All 128 Stage 1 claims verify.

## Status against the recommendations

| # | recommendation | state |
|---|---|---|
| 1 | explicit host + device admission | device bound (`AIUR_TRACE_SHARD_MAX_CELLS`) and host budget (`--max-ram`) are separate gates on every trace-sharded plan; the planner refuses a budget under the record plus the byte tables before it cuts anything |
| 2 | allocation / pinning reuse | done in the fork (pool threshold, slab, staged upload); traces generated straight into pinned storage is the next step |
| 3 | metadata-only lookup witness | `AIUR_TRACE_ONLY_LOOKUPS=1` hands the prover a shape-only witness (`LookupValues::shape_only`); the host stage-2 paths refuse it, so a backend that cannot evaluate the lookups on the device fails instead of proving an unbalanced argument |
| 4 | lookahead in both two-call APIs | done: STARK on a worker thread, caller's iterator/closure on its own thread, one witness ahead |
| 5 | chunk tuning for GPU consumption | 8 ordered chunks measured and verified; 4-vs-8 tuning remains open |
| 6 | record cache vs commitment retention | host record retention/eviction implemented; queue22 retained all 8 records while regenerating GPU commitments; broader retention-policy tuning remains open |
| 7 | LDE + Merkle kernel work | initial BLAKE3/NTT/LDE changes landed locally in ff3237c/f15a6c4 and measured in queue22; fresh profiling remains open |
| 8 | GPU range tree | measured and verified: queue22 3:41, two range leaves plus join/root; cross-command Stage 1/Stage 2 overlap remains open |

## Handoff

**Branch state.** ix `sb/aiur-trace-sharding-gpu` = `sb/aiur-distributed-execution`
(e3a29720) plus: trace-only lookup witness under the CUDA backend
(`AIUR_TRACE_ONLY_LOOKUPS=1`: a shape-only witness the host stage-2 paths
refuse) and the THP checklist; the budget-driven distributed driver;
measured-size admission with the RSS gate; the pointer namespace; the review
fixes above. multi-stark `sb/trace-sharding-gpu` = `sb/trace-sharding`
(9322ec06) plus pool retention, managed-slab control blocks, staged pinned
uploads, the STARK-on-worker-thread pipeline in `batch_round_one/two`, and
`LookupValues::shape_only`.
Build with `IX_CUDA=1 LIBCLANG_PATH=/usr/lib/llvm-18/lib lake build ix`; THP
must be `always` (§1.1). Recipes: `bench/trace-sharding-gpu-2026-09-11/`.

**What to know about execution memory.** There is no execution-size model
and no accounting inside the executor, by decision. `--exec-jobs` (default:
one per core) bounds how many workers execute at once; on a cold start that
first wave is admitted before any record is measured, so `--max-ram` does
not bound its peak. Once records are measured, `--max-ram` bounds what
runs ahead and what is retained: after every harvest the driver releases
retained records, furthest next use first, until what is charged fits the
budget (so an over-budget first wave is not carried through the barrier;
the released records re-execute for round two, on the CPU, behind the
prover), and an execution ahead must also fit beside the process's actual
RSS. Required executions are never refused, but retained records used
later are released first to make room for them. The hard limit is a cgroup cap;
`prove-distributed.sh` retries with `--exec-jobs` halved on a kill. For
Mathlib, choose `--exec-jobs` from the chunk sizes the manifest was cut for
(`ix prove --distributed --exec-only --out-ixes` measures them and writes
them into the manifest, where the prover reads them if present; that pass
costs one execution of every chunk) and run under the cap. Ordered waits are
accepted: round two proves in commit order; a slow chunk holds up later ready
ones.

**Not measured yet, in the order to take them.**

0. Done: the execute-ahead loop (5:04 on the min-cut four). Next on this
   path: start Stage 2 joins as soon as their two children are proven
   (the Stage 1/Stage 2 overlap, a scheduling question with independent
   claims), and the Mathlib run on a min-cut manifest sized from
   execution memory and `--exec-jobs`.
1. Stage 2 on the device is measured (above: 3:46 with two leaves and
   lookahead on the chunk batch; 2:51 with direct joins over four min-cut
   claims).
2. Blake3 row hashing was 43 % of GPU kernel time and radix-8 NTT 41 %;
   the first round of kernel work (fork ff3237c, f15a6c4) took the commit
   from 1.57 s to 1.32 s per Init shard. A fresh nsys kernel breakdown is
   the next step before more kernel work.
3. Chunking costs 21 extra shards on Init (56 vs 35 for one record: padding
   and duplicated memoization), ~100 s of the batch. Chunk count and
   balance (4 vs 8 ordered) is a measurement, not a setting.
4. The sppark NTT experiment (`aiur-gpu-upstream-review.md`) is bounded and
   legitimate, but a swapped NTT can give at most about a 2× win on the NTT
   itself, which is ~41 % of kernel time inside a commit that is ~1.4 s per
   Init shard: on the order of 0.3 s per commit, ~10 % of the Init prove,
   and at Mathlib scale (~25× the shards) still only a few minutes of wall
   clock. Take it after the above unless kernel time has become dominant.
5. Multi-GPU: one process per device with the preamble exchanged through
   files needs nothing from the protocol; the driver is single-device.
6. Trace generation straight into pinned memory and event-pipelined
   uploads: only if a profile shows the staging copy on the critical path.
