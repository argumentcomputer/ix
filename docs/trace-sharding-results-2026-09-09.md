# Trace sharding vs env sharding — Init, 2026-09-09

Box: Xeon 6975P-C, 64 logical cores, 495 GB, no GPU. Env `init-ts.ixe`
(65,994 constants) compiled at the branch's kernel. Baseline binary:
`sb/aiur-trace-sharding-design` @ 06089487 (pre-#619, so all proof sizes
are pre-grouping); planner runs: worktree `sb/aiur-trace-shard-planner`
(packing planner, piece-height cap, `AIUR_TRACE_SHARD_MAX_CELLS`). Every
run is one sequential systemd unit under a 480 GiB cap; logs in `logs/` (kept on the benchmark box, not in the repository),
summaries in `*-summary.log`. Whole-Init single execution: 6.0 min,
record 75 GiB, execute peak 85 GiB, monolithic projected peak 2352 GiB.

## Stage 1 (execute + prove), whole Init

| Config | Shards | Wall | STARK r1 + r2 | Peak RSS | Proof bytes |
|---|---|---|---|---|---|
| env 400 GiB | 9 | 32:46 | 432 + 1111 s | 343 GiB | 204 MiB (9) |
| env 200 GiB | 19 | 32:23 | 423 + 1099 s | 172 GiB | 420 MiB (19) |
| env 100 GiB | 45 | 34:36 | 447 + 1199 s | 87 GiB | 972 MiB (45) |
| trace 400, branch planner | 11 | 42:22 | 556 + 1605 s | 360 GiB | 41 MiB (1) |
| trace 200, branch planner | 44 | 38:03 | 464 + 1338 s | 189 GiB | 105 MiB (1) |
| trace 200, packing, no cap | 53 | 42:22 | 555 + 1610 s | 167 GiB | 73 MiB (1) |
| hybrid 4 env × trace 100, no cap | 4 × (29,31,31,25) | 47:26 | 626 + 1845 s | 95 GiB | 190 MiB (4) |
| **trace, 1.8 G cells (96 GB VRAM), cap 2^22** | **62** | **32:08** | 339 + 1006 s | 149 GiB | **79 MiB (1)** |
| trace, 1.8 G cells, cap 2^24 | 36 | 36:45 | 455 + 1372 s | 166 GiB | 62 MiB (1) |

Under `Retention::Regenerate` round 2 recommits stage 1, so r1 is paid
twice; net of that, trace shards do ≤ the env shards' STARK work at every
budget. Witness rebuilds are ~10 s/shard (~5 % of STARK).

## Stage 2 (ix_aggr, `--no-cache --jobs 1`, one 400 GiB slot)

| Leaves | Slots | Wall | Peak | Root |
|---|---|---|---|---|
| env 400 (9 × ~23 MiB) | 9 wraps + 8 joins | ~2.0 min/slot (7 of 17 measured, then stopped) ≈ 35 min | — | — |
| trace 400 batch (41 MiB, 11 shards) | 1 wrap | 4:38 | 333 GiB | 9.4 MiB |
| VRAM cap-22 batch (79 MiB, 62 shards), unsharded wrap | 1 wrap | OOM at 480 GiB after 3.5 min | >480 GiB | — |
| same, wrap proven as trace shards (`--trace-shards`) | 1 wrap = 4 shards | 12:10 | 266 GiB | 13.8 MiB |
| VRAM cap-24 batch (62 MiB, 36 shards), wrap as trace shards | 1 wrap = 3 shards | 9:12 | 245 GiB | 12.3 MiB |

## Findings

1. Env-shard Stage 1 wall is flat in the budget (32–35 min from 400 to
   100 GiB); its budget only buys proof bytes, which drive Stage 2 (≈2 min
   per slot here, 17 slots at 400, ~89 at 100).
2. The record floor: whole-Init trace shards keep the 75 GiB record
   resident, so a host budget of 100 GiB leaves ~25 GiB for phases (367–409
   shards). The GPU case is a device-cell budget with the record on the
   host, which is what the 1.8 G-cell rows measure.
3. Prover round-2 cost per committed cell on this CPU is set by the shard's
   tallest matrix: ~21 ns/cell at ≤2^22 rows, ~30 at 2^24, ~40 at 2^25.
   The packing planner must cap piece height (2^22 here); a GPU needs its
   own curve.
4. Packing planner (fewest fitting pieces, first-fit decreasing) vs the
   branch planner (every hot circuit split K ways): Σ active width 37.6k →
   32.9k (400), 88.8k → 40.3k (200), 1221k → 135k (100); padded cells
   −11…−15 % everywhere (whole circuits pad ~50 %). The offline harness
   (`plan_file` test) predicted the cap-22 round 2 within 4 %.
5. At the VRAM budget with the cap, whole Init: 32:08 Stage 1, 79 MiB of
   leaf proof, one sharded wrap of 12:10 → a 13.8 MiB root in ~44 min,
   against env-400's 32:46 + ~35 min and 204 MiB of leaves, with the
   Regenerate recommit still paid.
6. Wrapping a batch in circuit costs host RAM ∝ batch bytes (333 GiB at
   41 MiB, >480 at 79 MiB): recursion over VRAM-sized batches must itself
   be trace-sharded, as the design's §8.2 states; it works and costs 3–4
   wrap shards at 400 GiB.
7. Regenerate's recommit is ~20 % of STARK time at every budget; parking
   stage 1 (disk or host) is the remaining Stage 1 lever.

## Hybrid at the VRAM budget (2026-09-10, packing planner, cap 2^22)

Init in 4 env chunks, each a batch planned to 1.8 G cells:

| Stage | Result |
|---|---|
| Stage 1 | 76 shards (21, 20, 19, 16), 34:59 wall, 90 GiB peak, 104 MiB over 4 batch wrappers; STARK r1 + r2 = 456 + 1270 s |
| Stage 2, wrap-first (`--trace-shards`, 400 GiB slots) | 4 wraps + 3 joins, 21:23 wall, 295 GiB peak, 5.7 MiB root |
| Stage 2, direct joins | OOM at 480 GiB in the first join of two batch leaves (a direct join executes two batch verifications in one record) |

Against the whole-Init batch (62 shards, 32:08, 79 MiB, one sharded wrap of
12:10 → 13.8 MiB root): chunking costs ~9 % in Stage 1 and ~75 % in Stage 2
here, the price of three joins and four wraps against one wrap. This is the
shape a Mathlib chunk has today, and what the single-claim path (§13.3)
removes.

## Distributed execution, one claim (§13.3), 2026-09-10

Worktree `sb/aiur-distributed-execution`: Init over the 4-leaf manifest as
one `CheckEnv(root, none)` claim (`ix prove --distributed --cells
1800000000`), one worker record per leaf, all executed in parallel; the
claim digest equals the one-leaf manifest's.

| Quantity | Result |
|---|---|
| execution, 4 workers in parallel | 107 s (one execution 6.0 min; env-chunk sum 5.8 min) |
| records | 89,672,935,320 B total = 89.7 GB / 83.5 GiB (one execution historically reported at 75 GiB) |
| deferred calls | 38,326 from worker 0; 3,812 / 2,843 / 2,755 from workers 1–3 |
| shards | 71 (23, 17, 17, 14) |
| Stage 1 wall | 27:22 |
| peak RSS | 170 GiB (all four records resident) |
| proof | 100 MiB, one batch; `ix verify` 13.6 s |
| Stage 2, 400 GiB slots | one wrap of the 71-shard batch OOMs at 480 GiB (the 62-shard batch's wrap fit at 266 GiB) |
| Stage 2, 250 GiB slots (`--trace-shards --max-ram 250`) | one wrap, 6 wrap shards (heaviest projected 246 GiB), 15:27 wall, 216 GiB peak, 12.3 MiB root |
| Stage 1 again at a4b746a5 (inliner fix, range shapes) | 27:04 wall, 170 GiB peak, `ix verify` 13.8 s — the reordered bytecode costs nothing measurable |
| Stage 1 with records committed in caller order and re-executed for round two, prover waiting for each re-execution (`--exec-jobs 4 --no-prefetch`) | 33:21 wall, 159 GiB peak; round-one executions 90–111 s (four at once), round-two re-executions 78–96 s each, serial, 5.9 min of the 6.3 min added |
| same, the next worker executing while the prover works on the current record (`--exec-jobs 4`, the default; lock-free driver, dynamic dispatch) | 28:16 wall, 159 GiB peak, 99.8 MiB proof, same claim, `ix verify` ok; round-two re-executions 115–133 s each but overlapped, +4 % wall over the resident run |
| Stage 1 over 8 dependency-ordered chunks (`ix shard --ordered --shards 8`, commit 6bf0118d; `--distributed --cells 1800000000`, default exec-jobs and prefetch) | 37:25 wall, 113 GiB peak, 8 singleton caller groups so one record resident plus the prefetched next; records 10–23 GB (exec-only: 8 at once in 1:41, 153 GiB); 95 shards (21/14/12/12/10/9/9/8), 159.7 MiB batch, `ix verify` ok; round-one executions 61–106 s, round-two 55–100 s overlapped |

Init's four workers all call into each other, so they are one group: all
four records (83.5 GiB of retained record data) stay resident through the first record's
commitments, and the peak — records plus one shard's phases — moves only
from 170 to 159 GiB. Round two runs on one record at a time (26 GB plus
phases, plus the next record being executed ahead). The mechanism bounds
memory by the caller group, which on Init is everything; the gain
appears once ownership follows the dependency structure and groups are
small. With the next worker executed ahead, the re-executions cost 4 %
of wall (they run slower, 115–133 s against 78–96 s alone, because they
share the cores with the prover) instead of 23 %.

### Historical range-tree runs with the incorrect grouped-row estimator

| Configuration | Result |
| --- | --- |
| Stage 2 as a range tree, 6 leaves × 12 shards, 6 at a time (`--range 12 --jobs 6 --max-ram 480`) | OOM at 480 GiB during proving |
| same, 4 at a time (`--jobs 4 --max-ram 400`) | OOM at 480 GiB while the four leaves still executed |
| same, one node at a time (`--jobs 1 --max-ram 100`) | 19:40 wall, 285 GiB peak, 6.4 MiB root; leaves 233 / 113 / 129 / 130 / 119 / 124 s, five joins 58–59 s each, root 33 s (tree 19:34) |

The three tree runs were planned by an estimator that read a grouped
circuit's rows by circuit index (audit item A1): the recursion system
groups 174 circuits into 21, and a 12-shard leaf projected at 49–95 GiB
ran at up to 285 GiB, so every leaf was proven unsharded and the two
concurrent runs exceeded the box. With the estimator summing a group's
members (commit 8359f220) the same leaves are trace-sharded within their
100 GiB slice; the 4-wide rerun is below.

Even mis-planned and serial, the tree's root is half the wrap's proof
(6.4 against 12.3 MiB) at a wall 27 % above the whole-batch wrap, with
the leaves — 71 % of the tree's time — independent of each other.

### Corrected estimator: four-wide and serial Stage 2

| Configuration | Result |
| --- | --- |
| Stage 2 as a range tree at 8359f220, 4 nodes at a time within 100 GiB each (`--range 12 --jobs 4 --max-ram 400`) | 17:07 wall, 325 GiB peak, 7.0 MiB root, `ix codegen --check` clean; `ix verify --aggregate --ixe --ixes`: proof check 40 ms, 56,621/56,621 constants certified, 0 assumptions, 3.1 s wall |
| Stage 2 as a range tree at c6cb317a on the prefetch run's batch, one node at a time within 100 GiB (`--range 12 --jobs 1 --max-ram 100`, the single-slot measurement) | 25:45 wall, 88.5 GiB measured process peak, 96.1–99.2 GiB projected per-node prover peaks; same 7.0 MiB root, `ix verify --aggregate` OK in 39 ms proof-check time; every node cut into 2–3 trace shards |

| env-400 end to end on the same code (f5f62c17): Stage 1 `ix prove --ixes init-env400-measured.ixes --max-ram 400` | 33:21 wall, 347 GiB peak, 9 proofs of 10.7–11.0 MiB, 96.8 MiB in all (post-grouping; the 204 MiB figure above predates it) |
| env-400 Stage 2, wrap-first, `--jobs 4 --max-ram 400` (two 195 GiB wraps at a time) | 14:19 wall, 197 GiB peak, 9 wraps + 8 joins, 5.86 MiB root, `ix verify --aggregate` ok |

Side by side on commit f5f62c17, same env and inputs:

| | Stage 1 | Stage 2 | end to end | leaf bytes | root | box peak |
|---|---|---|---|---|---|---|
| env shards, 400 GiB slots, 9 shards | 33:21, 347 GiB | 14:19, 197 GiB (2 slots at a time under 400 GiB) | 47:40 | 96.8 MiB | 5.86 MiB | 347 GiB |
| trace shards, 1.8 G cells, 71 shards, 4 workers | 28:16, 159 GiB | 25:45, 88.5 GiB (one 100 GiB slot) | 54:01 | 99.8 MiB | 6.95 MiB | 159 GiB |

With grouped circuits the env leaves are 10.7 MiB each, so the two paths
now carry the same leaf bytes and the env root is smaller. The trace
path's advantage is memory: it runs both stages inside 159 GiB (Stage 2
inside 89 GiB), where the env path needs 347 GiB for Stage 1 and 195 GiB
per wrap, and it is 13 % slower end to end because its recursion nodes
are trace-sharded to the slot.

Both runs produced root address
`f92488191191920664d2daaece1470e79bd1c26ad706541055f7a6710911fd19`.
The serial verifier reports exact coverage of 56,621/56,621 environment
constants and zero assumptions. The earlier inventory count of 65,994 in
this file's heading has not been reconciled here; identify comparisons by
input hashes and authenticated claims, not by silently equating those counts.

The log label `query-record peak` is a model projection returned from the
record-based prover planner, not sampled RSS or the record's own storage.
For example, the first leaf retains 8.04 GB (7.49 GiB) of record data and
projects a heaviest-shard prover peak of about 96.9 GiB. The whole serial
process measured 92,801,132 KiB maximum RSS, or 88.5 GiB. Thus there is no
contradiction between the 96–99 GiB per-node projections and the lower
measured process peak.

Per node, with the corrected estimator (whole-execution peaks 195–389 GB
for a 12-shard leaf, ~205 GB for a join, 110 GB for the root, every node
cut into 2–3 trace shards within its 100 GiB slice):

| Level | Nodes | Wall each | Concurrency |
|---|---|---|---|
| leaves | 6 × 12 shards | 234–343 s (first four), 182–215 s (last two) | 4, then 2 |
| joins | 3 | 172–184 s | 3 |
| joins | 2 | 97–98 s | 2 |
| root | 1 | 86 s | 1 |

The serial nodes ran faster individually than the four-wide nodes, which
shared the box's CPU resources. Four-wide saved 8:38 of total wall while
using about 3.7x the measured peak RSS (four times the nominal slot budget).
Do not infer a fourfold speedup from four slots, or an intrinsic 3x
trace-sharding penalty from comparing earlier serial unsharded joins with
four-wide sharded joins. Regenerate rebuilds shard witnesses and first-pass
commitments from the record; it does not rerun the entire verifier execution
once per trace shard on this path. Level barriers still leave slots idle.

The recursion records are relatively small (about 4–8 GB for these leaves),
and the corrected planner demonstrably fits this serial Stage 2 into a
100 GiB slot. This remains an empirical result, not a proof that any input
can fit an arbitrary budget or that host RSS and GPU VRAM are interchangeable.

### Historical comparison to the four-env-chunk hybrid

Against the hybrid on the same chunks (34:59 + 21:23 = 56:22): 27:22 +
15:27 = 42:49, −24 %, and one proof instead of four wraps and three
joins. The wrap's footprint is set by the slot budget, not the batch: at
250 GiB slots the planner cut the wrap into six shards where 400 GiB slots
had no room for the record and two shards at once. A batch this size is
still one recursion proof verifying 71 shards; the range-sum recursion
(§13.2) splits that across proofs a machine of any size can take.

## Not measured here

GPU per-cell-vs-height curve and cell-to-VRAM calibration, `Retention::Retain`
at scale, InitStd/Lean/Mathlib, env-shard direct joins on the current
revision, and a Stage 1 with both records and phases below 100 GiB of host
RSS (the ordered layout's 113 GiB is two records plus one shard's CPU
phases). See [the handoff](trace-sharding-handoff.md) for what a GPU box
should calibrate.
