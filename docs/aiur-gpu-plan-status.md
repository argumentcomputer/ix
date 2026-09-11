# Trace-sharded Aiur on GPU: measured ladder and status

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
not the flag. This is the accepted trade: `--exec-jobs` bounds the first
wave, `--max-ram` bounds admission and retention once sizes are known, the
cgroup cap is the hard limit, and the recipe halves `--exec-jobs` on a
kill. For Mathlib set `--exec-jobs` from the chunk sizes the manifest was
cut for, and run under the cap.

## Status against the recommendations

| # | recommendation | state |
|---|---|---|
| 1 | explicit host + device admission | open; `--cells` still a work cap, host budget unenforced, planner floor check pending |
| 2 | allocation / pinning reuse | done in the fork (pool threshold, slab, staged upload); traces generated straight into pinned storage is the next step |
| 3 | metadata-only lookup witness | prototype only (`AIUR_TRACE_ONLY_LOOKUPS`, skips writes, still allocates lazily); needs a backend capability with a fallback contract in multi-stark |
| 4 | lookahead in both two-call APIs | done: STARK on a worker thread, caller's iterator/closure on its own thread, one witness ahead |
| 5 | chunk tuning for GPU consumption | measuring: 8 ordered chunks queued, 4 next |
| 6 | record cache vs commitment retention | open |
| 7 | LDE + Merkle kernel work | open; stage-1 commit is at its kernel floor (~1.4 s: blake3 44 %, radix-8 40 %) |
| 8 | GPU range tree | open; not yet run on the device |

## Handoff

**Branch state.** ix `sb/aiur-trace-sharding-gpu` = `sb/aiur-distributed-execution`
(e3a29720) plus: trace-only lookup witness under the CUDA backend
(`AIUR_TRACE_ONLY_LOOKUPS=1`, prototype: it skips the host lookup writes but
multi-stark has no capability/fallback contract for it yet) and the THP
checklist; the budget-driven distributed driver; measured-size admission with
the RSS gate. multi-stark `sb/trace-sharding-gpu` (ac144be2) = `sb/trace-sharding`
(9322ec06) plus pool retention, managed-slab control blocks, staged pinned
uploads, and the STARK-on-worker-thread pipeline in `batch_round_one/two`.
Build with `IX_CUDA=1 LIBCLANG_PATH=/usr/lib/llvm-18/lib lake build ix`; THP
must be `always` (§1.1). Recipes: `bench/trace-sharding-gpu-2026-09-11/`.

**What to know about execution memory.** There is no execution-size model
and no accounting inside the executor, by decision. `--exec-jobs` (default:
one per core) bounds how many workers execute at once; on a cold start that
first wave is admitted before any record is measured, so `--max-ram` does
not bound it (Init at `--max-ram 100` still peaked at 189 GiB). Once records
are measured, `--max-ram` bounds what runs ahead and what is retained for
round two, and an execution ahead must also fit beside the process's actual
RSS. Required executions are never refused. The hard limit is a cgroup cap;
`prove-distributed.sh` retries with `--exec-jobs` halved on a kill. For
Mathlib, choose `--exec-jobs` from the chunk sizes the manifest was cut for
(`ix prove --distributed --exec-only --out-ixes` measures them and writes
them into the manifest, where the prover reads them if present; that pass
costs one execution of every chunk) and run under the cap. Ordered waits are
accepted: round two proves in commit order; a slow chunk holds up later ready
ones.

**Not measured yet, in the order to take them.**

1. Stage 2 on the device: `ix aggregate --range N --trace-shards` over the
   distributed batch has only CPU numbers (25:45 for the 71-shard batch on
   the 64-core box). It is the larger unknown end to end; the aggregate
   command takes its cell budget from `AIUR_TRACE_SHARD_MAX_CELLS`.
2. Blake3 row hashing is 43 % of GPU kernel time and radix-8 NTT 41 %; the
   commit is at that kernel floor (1.4 s per Init shard). Kernel work starts
   with Blake3.
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
