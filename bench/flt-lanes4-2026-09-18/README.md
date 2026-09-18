# Anthropic FLT proven on four GPUs: 572 shards, three executions per lane

**Result (2026-09-18):** the Anthropic FLT environment (1,330,204 constants,
30.1 GB `.ixe`) proven end to end on four RTX PRO 6000 Blackwell in one
process, on the byte-seeded 572-shard manifest with the sppark-only backend
and lightweight metrics. Root
`7d44c48ee47c2ad9d5f1ae939bbbec7e6036e6ac8ce4511a9428e5adafe55dc0`
verified, composed verdict OK, root proof 6,025,664 bytes (5.75 MiB), zero
growth waits, zero contention retries.

**Representative prover time: about 5 h 0 min** (17,960 s), the time the
run would have taken had one leaf not crossed the 128 GiB per-record
ceiling. **Actual elapsed: 5 h 48 min**, including four refinement rounds
on that leaf, a stop, and a restart under a 256 GiB ceiling. Both are
composed from the same logs, as set out below.

## Timeline

| Event | Prover clock |
|---|---:|
| Budget line (after the environment load, about 5 min) | +0 |
| First claim proven | +218 s |
| 100 / 200 / 300 / 400 / 500 claims proven | +1,606 / +4,381 / +7,208 / +9,911 / +12,535 s |
| Claim 570 dispatched (711 blocks) | +16,091 s |
| All other claims proven | +16,499 s |
| Claim 570 crosses the 128 GiB ceiling; drain and bisection | +16,750 s |
| Three more rounds: halves of 23.2, 10.3, 6.0 and 2.6 GiB peel off, the core stays over the ceiling | to +18,800 s |
| Process stopped; refined checkpoint set aside; restart on the original partition with `AIUR_RECORD_MAX_BYTES` = 256 GiB | 04:51 UTC |
| Restart: 571 claims reused, 7 cached join subtrees; claim 570 executes whole | +11 s |
| Claim 570 executed: 174.2 GiB in 915 s; proven in 259 s | +927 s, +1,187 s |
| Root dispatched / proven (8 path joins, 139 s root execution, 3 wraps) | +1,627 s / +1,882 s |

The representative time is the original clock to claim 570's dispatch
(16,091 s) plus the restart's measured execution and proof of the whole
leaf (1,174 s), the path joins and root above it (695 s), which is what the
original run would have done from +16,091 s under a 256 GiB ceiling with
the other lanes finishing their last claims by +16,499 s.

## Per unit

| | Claims (571, excluding leaf 570) | Leaf 570 whole | Joins (571) | Root |
|---|---:|---:|---:|---:|
| Execution mean / max | 293 s / 928 s | 915 s | 50 s / 139 s | 139 s |
| Record mean / p50 / p90 / p99 / max | 31.8 / 30.1 / 44.0 / 64.5 / 89.5 GiB | 174.2 GiB | 15.5 GiB | 41.1 GiB |
| Proof mean / max / total | 55.7 s / 156.5 s / 31,799 s | 259 s | 23.4 s / 48.9 s / 13,444 s (incl. wraps) | 118 s incl. 3 wraps |
| Trace shards per plan, mean | 12.4 (claims and joins) | ~110 | | |

Claims over the 36.5 GiB reservation: 127 of 572. Over 64 GiB: 7, plus
leaf 570. GPU proving work 45,500 s, about 11,400 s per lane over the
representative 17,960 s: 63% occupancy, execution-bound throughout at
three executions per lane, with executions at 5.3 : 1 against proofs.
Mean sampled GPU utilization 39 to 42%, device memory peak 69.8 GiB.
Peak process RSS 811 GiB under the 920 GiB scope (the environment's
residency of about 65 GiB sits on top of the record pool). Disk: the
lanes cache holds 575 claim proofs and 563 join entries, 126 MB.

Against Mathlib on the same tree (78 shards, three executions per lane,
2,396 s): records match at the median (30.1 against 28.0 GiB) but FLT's
tail is far heavier (p90 44 against 33 GiB, p99 64 GiB, one leaf at
174 GiB), executions are 20% dearer per claim (293 against 244 s), and
proofs per claim match (55.7 against 52.4 s). The byte model that sized
the cut holds for the bulk and fails for the tail.

## The 174 GiB leaf

Leaf 570 held 711 blocks, 18.8 MB, an ordinary shard by every static
measure. Its record needed 137.4 GB, 29 bytes over the 128 GiB ceiling.
Four rounds of byte-balanced bisection peeled off halves of 23.2, 10.3,
6.0 and 2.6 GiB while the remainder stayed over the ceiling, because the
cost is concentrated in 586 blocks totalling 3.5 MB: private lemmas of
the Vélu-isogeny solutions in `P2M.Sol.S_WeierstrassCurve_…velu…`
(`leaf570-velu-names.txt`), polynomial identities over Weierstrass
curves whose kernel checks reduce heavily, about 0.3 GiB of record per
constant on a few kilobytes of term, 25 times the byte model. Each
refinement round idled the whole box for ten to fifteen minutes: the
drain, the light half's execution, and the heavy half's re-execution to
the ceiling.

Under a 256 GiB ceiling the leaf executes whole in 915 s and proves in
259 s, so the ceiling, not the leaf, was the problem. Three changes
follow:

1. Size the per-record ceiling from the pool rather than a constant. At
   a 731 GiB pool, 256 GiB is safe: the record a prover needs is never
   refused and the others wait. `run-lanes4.sh` takes `RECORD_MAX_GIB`
   for it; use 256 for FLT.
2. Admit on measured occupancy, and stop admitting once any record passes
   a soft threshold, so a large record grows without draining the box.
3. Cut with measured costs. `ix profile` run afterwards ranks this leaf
   first at a predicted 172 GiB (next section); a profiled cut weighted
   by bytes and `nat_arith` would have spread the Vélu cluster across
   leaves.

## Would the out-of-circuit profile have caught it?

Yes. `ix profile anthropic-flt.ixe` (the Rust kernel over every constant,
96 workers, caches dropped) took 11:21 wall, 457 s of it the parallel
pass, 116 GiB peak RSS, and wrote a 361 MB `.ixprof` with per-block
heartbeats, serialized size and the kernel's `subst`, `whnf`, `def_eq`,
`nat_arith` and `intern` counters. Summed per leaf of the 572-shard
manifest and set against the 572 records the run measured
(`profile_vs_records.py`):

| Predictor of a leaf's record | Correlation over 572 leaves | Leaf 570's rank |
|---|---:|---:|
| serialized bytes | 0.57 | 337 |
| heartbeats | 0.25 | 16 |
| `whnf` | 0.27 | 7 |
| `nat_arith` | 0.56 | **1** |
| bytes + `nat_arith`, least squares | **0.79** | **1** |

The two-term fit is 1,770 record bytes per serialized byte plus 2,452
record bytes per `nat_arith` operation. The first term is the byte model
the cut was seeded with; the second is what it lacked. Under it:

| Leaf | Predicted | Measured |
|---:|---:|---:|
| 570 | 172.2 GiB | 174.2 GiB |
| 357 | 96.6 GiB | 89.5 GiB |
| 557 | 93.2 GiB | 88.0 GiB |
| 404 | 72.8 GiB | 71.4 GiB |
| median / p90 | 29.9 / 42.6 GiB | 30.2 / 44.1 GiB |

The top four and the body of the distribution are right; leaves 160, 472
and 287 (75, 75 and 64 GiB measured) are under-predicted at 29 to 44 GiB,
so a third term is missing for part of the tail. But the question was
whether the profile flags the leaf that broke the run, and it does, as the
single most expensive leaf by a factor of 1.8, at a predicted record above
the 128 GiB ceiling, eleven minutes after the environment was compiled.

Why `nat_arith`: the Vélu lemmas evaluate polynomial coefficients as
natural-number arithmetic that the Rust kernel does natively and cheaply,
which is why heartbeats rank the leaf only 16th, while the IxVM proves
each such operation through its byte and memory gadgets, and the record
counts every one. The same asymmetry sends the two singleton leaves the
other way: cheap for the kernel, large for the record because their bytes
are ingressed and hashed in circuit.

### Best fit over the profile's counters

Exhaustive search over subsets of up to four of fourteen per-leaf features
(bytes, frontier bytes, block count, `Σ size^1.5`, the six kernel counters,
and unfolded-producer bytes and delta-edge counts from the profile's
delta graph), non-negative least squares, leave-one-out over the 572
leaves (`best_fit.py`, on top of `record_model.py`):

| Model | LOO r | median error | p90 error | heaviest 20 in predicted top 40 |
|---|---:|---:|---:|---:|
| bytes | 0.57 | 3.7 GiB | 10.1 GiB | |
| bytes + `nat_arith` | 0.79 | 3.7 GiB | 9.9 GiB | 12 |
| bytes + frontier + `subst` + `nat_arith` | **0.82** | **3.1 GiB** | **9.1 GiB** | 10 |

The four-term fit is 1,205 record bytes per serialized byte, 570 per
frontier byte, 502 per `subst` and 2,487 per `nat_arith`. Heartbeats,
`whnf`, `def_eq`, `intern`, block count, the superlinear term and the
delta-graph features add nothing once these are in. It places leaf 570
first (169 against 174 GiB) and 557, 357, 500 and 404 in the top five. It
misses one family: leaves 160, 476, 440, 287 and 472, measured 60 to
75 GiB, predicted 29 to 45. Leaf 160 is `P2MW` Drinfeld-curve and
algebraic-curve lemmas (`leaf160-names.txt`) and its record is dominated
by function circuits 112, 156, 110, 109 and 111, a mix no other leaf has;
naming those circuits from the IxVM toplevel's function order would name
the counter the profile lacks. Until then the model under-predicts about
one leaf in a hundred by a factor of two, which is what a margin on the
ceiling is for. For flagging, `bytes + 2.1 × nat_arith` over three times
the median marks a leaf to split or isolate before the run.

The profiled cut, `ix shard --profile`, balances on heartbeats today.
Balancing on `bytes × 1,770 + nat_arith × 2,452` instead would have spread
the Vélu cluster and the singletons across leaves in the first cut.

## Inputs, build and commands

| Item | Value |
|---|---|
| `anthropic-flt.ixe` | sha256 `5251edf00c0050d766702cd32d777b30889c167f4e0021b5ba89496abbb2f4d8` |
| `anthropic-flt-572.ixes` | sha256 `1207ceb0bddd165ac263f94e6e79dc3e7a8dfb04a1cf598da20e6c7be3ee2d6b`, seeded by `ix shard --max-ram 230 --exec-jobs 3` (`../flt-shard-plan-2026-09-17`) |
| ix | `7bd17307` (this branch merged with upstream `2ba81a1b`), multi-stark `59df87a4`, sppark for every transform; features `parallel,cuda,cuda-trace-codegen,net`; binary sha256 `bf1d6753…` |
| Host | 4× RTX PRO 6000 Blackwell Server Edition, 96 CPUs, 999 GiB; THP `always` / `defer+madvise`; driver 595.91.07, CUDA 13.3 |
| Environment | `AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000 AIUR_METRICS=<run>/metrics.jsonl`, `LD_PRELOAD=libcuda.so.1` |
| Run | `ENV_DIR=~/benchdata/flt IXE=anthropic-flt.ixe IXES=anthropic-flt-572.ixes EXEC_JOBS=3 run-lanes4.sh flt572-lanes4-exec3`: `systemd-run --scope -p MemoryMax=920G -- ix prove --trace-shards --lanes 4 --exec-jobs 3 --max-ram 230` |
| Restart | same command and cache directory, refined checkpoint moved aside, `AIUR_RECORD_MAX_BYTES=274877906944` |

The five outlier leaves proven earlier on one GPU (`../flt-shard-plan-2026-09-17`)
were not reused: they predate the sppark and multi-stark changes.

Files: `flt572-lanes4-exec3-meta.txt`, `flt572-lanes4-exec3-summary.txt`,
`leaf570-velu-names.txt`, `run-lanes4.sh`, `profile.log`,
`profile_vs_records.py`, `record_model.py`, `best_fit.py` (read the
`.ixprof`, the manifest, the lanes logs and the metrics; the `.ixprof` is
in `~/benchdata/flt/` and regenerates from the `.ixe` in 11 minutes),
`leaf160-names.txt`. Raw logs, both metrics files,
GPU samples and the lanes cache are in
`~/benchdata/flt/runs/flt572-lanes4-exec3/` on the four-GPU box.
