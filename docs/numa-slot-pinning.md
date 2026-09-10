# Design: per-slot NUMA pinning for `ix aggregate` (and lanes for `ix prove`)

Status: IMPLEMENTED 2026-09-08 (uncommitted; see §10 for measured results). Author: claude (session with S. Burnham). Targets
`crates/ffi/src/aiur/aggregate.rs::run_scheduler` + a new `crates/ffi/src/numa.rs`.
Coordinate with the agent working in `aggregate.rs`/`shard_pipeline.rs`: this design
does not touch `prove_aggregate`, `aggregate_io`, replay, or the shard pipeline.

## 1. Why (measured)

| fact | measurement |
|---|---|
| one prove cannot use more than one domain | E1: full box 1.08–1.18x over one 64-thread lane |
| isolated lanes scale perfectly | E1(c): three membind lanes = 3.00x, zero per-lane slowdown |
| in-process slots interfere | InitStd Stage 2: `ix_aggr` join 85 s solo vs 133–159 s with 3 live; direct join ~310 s with 3 live; ⇒ ~0.55x per slot, **~1.7x aggregate at `--jobs 3`** |
| cross-domain memory is not the main cost | interleave vs membind ≈ 10 % (m2/m5/m12) |
| so the loss is shared rayon pool + unplaced memory | three slots' `par_iter` work interleaves on 192 threads; first-touch places each slot's buffers wherever the faulting thread ran |

Goal: make each admitted slot behave like an E1 lane — its own 64 threads, its own
domain's memory — inside the single `ix aggregate` process (no env reload, no IPC,
no extra binaries). Expected: Stage 2 ≈ 3.0x at three slots instead of ≈ 1.7x.

## 2. Mechanism

Linux gives everything needed per thread: `sched_setaffinity(2)` (CPU set) and
`set_mempolicy(2)` (`MPOL_BIND`/`MPOL_PREFERRED` to a node mask). Both are
per-task, inherited by nothing — so they must be applied on every thread that
allocates or computes for the slot. Rayon lets us do exactly that: a
`ThreadPool` built with `.start_handler(|i| pin(domain))` runs the pin on each
worker at spawn, and `pool.install(f)` runs `f` on a worker of that pool, so every
`par_iter` reached from inside `f` — the whole multi-stark prover — executes on
that pool. mimalloc's huge objects are fresh `mmap`s freed on drop (memcfg
series), so their pages are first-touched by pool threads and land on the bound
node; per-thread small heaps are local by construction. THP faults honor the
policy.

```
run_scheduler
  ├─ topology = numa::detect()            // sysfs; honors current cpuset; 1 node ⇒ no-op
  ├─ pools[k]  = numa::pool(domain k)     // lazy, 64 threads, start_handler pins
  └─ admit slot → choose domain k (RAM-aware, §4)
       scope.spawn(move || {
           numa::pin_current_thread(k);   // advice/child-proof decode/persist allocate locally
           pools[k].install(|| prove_slot(ctx, index, &children))   // prover on domain k
       })
```

## 3. Module `crates/ffi/src/numa.rs` (~150 lines, no new deps; `libc` is already a workspace dep)

```rust
pub struct Domain { pub node: u32, pub cpus: Vec<usize>, pub mem_bytes: usize }
pub struct Topology { pub domains: Vec<Domain> }              // empty ⇒ pinning disabled

pub fn detect() -> Topology
  // /sys/devices/system/node/node*/cpulist  ("0-31,96-127")
  // /sys/devices/system/node/node*/meminfo  ("Node 0 MemTotal: N kB")
  // intersect each cpulist with sched_getaffinity(0) so `numactl`-launched or
  // cgroup-limited processes only see their allowed CPUs; drop empty domains;
  // if <2 domains remain ⇒ Topology{domains: []}.
  // Env: IX_NUMA=off disables; IX_NUMA=auto (default).

pub fn pin_current_thread(d: &Domain, policy: Policy)         // Policy::Bind | Policy::Preferred
  // sched_setaffinity(0, cpu_set of d.cpus); set_mempolicy(MPOL_BIND|MPOL_PREFERRED, &[1<<d.node], 64)
  // via libc::syscall(libc::SYS_set_mempolicy, mode, mask.as_ptr(), maxnode)

pub fn pool(d: &Domain, policy: Policy, threads: usize) -> rayon::ThreadPool
  // ThreadPoolBuilder::new().num_threads(threads).thread_name(|i| format!("numa{}-{i}", d.node))
  //   .start_handler(move |_| pin_current_thread(&d, policy)).build()

pub fn unpin_current_thread()                                 // affinity = all allowed; MPOL_DEFAULT
```

Policy default `Bind` (max throughput; the RAM gate uses estimated weights). `Preferred`
(env `IX_NUMA_POLICY=preferred`) spills to other nodes instead of failing when a
domain is full — the safe mode for untrusted weights.

Threads per pool: the domain's full cpuset (64 = 32 cores × 2 HT). m7/m8 vs m12
showed 32 vs 64 within noise under THP; 64 is the default, `IX_NUMA_THREADS`
overrides.

## 4. Scheduler changes (`run_scheduler`, ~60 lines)

Today: one global `reserved`/`budget` (`--max-ram`, default 92 % MemTotal),
heaviest-ready-first, `--jobs` cap, "over-budget slot runs alone".

New state when topology is non-empty:

```
domain_budget[k] = min(domain.mem_bytes × 0.90, budget)   // ≈ 460 GiB here
domain_reserved[k], domain_active[k]
```

Admission for a ready slot of weight `w` (still heaviest first):

1. candidates = domains with `domain_reserved[k] + w ≤ domain_budget[k]` and global `reserved + w ≤ budget`.
2. prefer an **idle** domain (`domain_active[k] == 0`); among those the most free RAM.
3. else, if `IX_NUMA_PACK != 0` (default 1), the domain with the fewest active slots that fits — two 195 GiB slots may share a domain (PR #598 Init report: 2 proves on one 64-thread box = 1.53x, i.e. still +50 % throughput; a 390 GiB direct join never shares).
4. none fits and nothing active ⇒ the existing over-budget rule: run alone, **unpinned with `MPOL_PREFERRED`-interleave semantics** (`numa::unpin_current_thread`, global pool) so a giant slot can use all memory.
5. `max_jobs` default (when `--jobs 0`) becomes `domains × (pack ? 2 : 1)` instead of "all ready slots".

Slot completion releases both the global and the domain reservation. Placement is
logged: `[aggregate] slot N: admitted W GiB on node K; node reserved r/b GiB; active a/m`.

Nothing else changes: `prove_slot`, cache, persistence, replay, `--plan-only`,
the Lean-side plan simulation (`runAggregateDag`) and the FFI signature are
untouched. Configuration is env-only for the first cut (`IX_NUMA`,
`IX_NUMA_POLICY`, `IX_NUMA_PACK`, `IX_NUMA_THREADS`); a `--numa` CLI flag can be
added once the FFI/Lean side is quiet.

## 5. Memory-placement details that decide whether this reaches 3x

- **Everything the slot allocates must happen on a pinned thread.** The scope
  thread is pinned before `install`, so `aggregate_io` (advice + child-proof
  decode), the public-input packing, and `persist_cached` are local. Inside
  `install`, all multi-stark `par_iter`s run on pool workers (pinned).
- **Children's proofs live on the child's domain** (`Arc<Slot>` holds the proof
  bytes). A parent reads 8–25 MB remotely once; negligible.
- **mimalloc reuse across slots**: freed small-object pages sit in per-thread
  heaps (local); huge buffers are unmapped on free, so a later slot on another
  domain never inherits remote pages. Verified by the fault counts: with THP the
  process faults ~0.7 M pages per bench, i.e. buffers really are fresh each phase.
- **Global rayon pool remains** for the deterministic prepare/plan work (unpinned);
  it is idle during proving.
- **Verify with** `numastat -p <pid>` during a run (each live slot's memory should
  sit on one node) and `AnonHugePages` ≈ RSS in `smaps_rollup`.

## 6. Failure modes

- `MPOL_BIND` + domain full ⇒ the kernel OOM-kills the process (there is no swap),
  taking all live slots with it; the aggregate cache resumes completed slots. The
  original 195 GiB structural weight underestimated upper Mathlib joins and
  caused this failure on 2026-09-09; see §12 for the corrected model.
  `IX_NUMA_POLICY=preferred` trades ~10 % for graceful spill.
- A panic inside `install` propagates to the scope thread and is caught by the
  existing `catch_unwind`; the pool stays usable.
- 1-node hosts (CI, laptops): topology empty ⇒ byte-identical behavior to today.
- Running under `numactl --cpunodebind=k`: `sched_getaffinity` intersection leaves
  one domain ⇒ pinning disabled, behaves as today.

## 7. Expected numbers

Solo per-slot rates (from pass A's root slots and the 0.55x ratio): `ix_aggr` join
≈ 85 s, wrap ≈ 85–90 s, direct join ≈ 170 s (only the 3-way 310 s is measured; solo
is inferred).

| | today (`--jobs 3`, 1.7x) | pinned (3 idle domains) | pinned + pack (2×195 per domain) |
|---|---:|---:|---:|
| InitStd Stage 2 (pass A shape) | 1244 s measured | ≈ 700 s | ≈ 650 s |
| Mathlib Stage 2 (123 direct + 122 aggr joins) | ≈ 5.5 h | ≈ 2.9 h | ≈ 2.6 h |

Acceptance test: rerun InitStd pass A (`--direct-joins --jobs 3 --max-ram 1300`,
cache cleared or `--no-cache`) — target ≤ 750 s, per-slot times within 15 % of
solo, `numastat -p` showing one node per live slot.

## 8. Follow-up: Stage 1 lanes in one process

`ix prove --ixes --shards …` currently needs three `numactl` processes (three env
loads, three manifests to reconcile). With `numa.rs`, the shard pipeline in
`shard_pipeline.rs` can own one lane per domain (each lane = a pinned pool +
pinned consumer thread + its lookahead executor), giving `ix prove --lanes 3` with
one env load and one `--out-ixes`. Same module, same pin helpers; do it after the
other agent's pipeline lands.

## 9. Alternatives considered

- **Per-domain worker processes** (controller spawns `numactl`'d children, IPC over
  a pipe): equally 3.0x, better crash isolation, and the natural step to
  multi-box; but each worker reloads the 3.3 GB env or must be long-lived with a
  slot protocol — more code and a second binary path. Not needed for one box.
- **`numactl` on the whole aggregate process**: caps it at one domain. No.
- **libnuma**: unnecessary; two syscalls and two sysfs files cover it.

## 10. Implementation and measured results (2026-09-08 20:40–22:00 UTC)

Implemented as designed: `crates/ffi/src/numa.rs` (topology, pin helpers, pools;
env knobs `IX_NUMA`, `IX_NUMA_POLICY`, `IX_NUMA_THREADS`, `IX_NUMA_PACK`),
`run_scheduler` in `aggregate.rs` (`NumaLane`, `choose_numa_lane`, `numa_lanes`,
per-lane budgets, pin + `install`, per-slot completion log lines, and one rule
beyond the design: a slot that is the only runnable work with nothing live runs
**unpinned**, because a solo pinned slot is ~12 % slower than a solo unpinned
one). `libc` added to the ffi crate. fmt/clippy(-D warnings)/unit tests pass.

Controlled InitStd Stage 2 (15 leaves, direct joins, `--max-ram 1300`,
`--no-cache`, same binary):

| run | wall | vs unpinned |
|---|---:|---:|
| `IX_NUMA=off --jobs 3` | 1265.6 s | 1.00x |
| pinned `--jobs 6` (pack) | 1033.6 s | **1.22x** |

Per slot: direct join 289–332 s unpinned (2 others live) → **209–223 s pinned,
flat under load** (= solo speed, 1.45x). `ix_aggr` join: 136–176 s unpinned with
others → 149 s pinned when packed two per node, 95–103 s pinned alone vs 83–88 s
unpinned alone. Placement verified with `numastat -p` (293/291/281 GB on nodes
0/1/2, one direct join each) and per-thread `Cpus_allowed_list`.

Why 1.22x and not 1.7x: the interference removed was 1.45x per slot (the solo
direct join is ~210 s, not the 170 s §7 inferred), and on a 15-leaf tree the
serial dependency tail (last ~5 slots) is a third of the wall. On Mathlib
(246 leaves) the parallel phase dominates: **Stage 2 ≈ 3.6 h pinned vs ≈ 5.3 h
unpinned**.

## 11. Half-pools for packed slots (2026-09-08 22:30–23:07 UTC)

`IX_NUMA_SPLIT` (default on): each domain's physical cores are split into two
halves (HT siblings kept together, via sysfs `thread_siblings_list`); a lane owns
two 32-thread half-pools besides its full pool. Light slots that pack take a free
half; heavy or lone slots keep the full pool. Wrap-first pinned InitStd Stage 2:

| | wall | packed slot time |
|---|---:|---:|
| shared 64-thread pool | 977.6 s | 96–347 s (median 160) |
| core-disjoint half-pools | **938.0 s** | 104–159 s (median 136) |

With isolation + packing, wrap-first (six 195 GiB slots live) beats direct joins
(three 390 GiB slots live) by 8 % (938 vs 1018–1036 s), reversing the unpinned
ordering. The user chose to keep direct joins as the Stage 2 mode (wrap-first recorded for information); half-pools then apply to the upper `ix_aggr` joins.

## 12. Subject-aware structural reservations (2026-09-09)

The first Mathlib attempt packed slots 140 and 355 onto node 0, reserving
195 GiB each against a 453.3 GiB node budget (~504 GiB physical). Slot 140
has 187,668 subjects; slot 355 has 13,023. The subsequent run with packing
disabled completed slot 140 with a query-record prediction of 383.4 GiB and
a sampled node resident peak of 362.0 GiB. Global slice headroom could not
help allocations bound to that node.

The shape-9 weight is now **195 GiB + 1.25 MiB × subject count**, with a
**390 GiB minimum above 65,536 subjects**, shared by the Rust scheduler and
Lean reference scheduler. The subject term covers growth through the
187,668- and 314,195-subject joins. The minimum covers a separate jump:
slot 337 predicted 380.5 GiB at 91,068 subjects, compared with slot 62's
256.5 GiB at 91,620 subjects. A linear term alone underestimated slot 337
and slot 265. This model covers the observed peaks; it is not a least-squares
fit. The structural subject-root fold is constant work, but assumption/path
checks and recursive verification of growing children are not. Trace padding
also makes peaks grow in steps.

Representative shape-9 measurements from
[`stage2-mathlib.log`](../logs/stage2-mathlib.log), matching plan subject counts
with completed proof `peak` entries:

| slot | subjects | query-record predicted peak (GiB) | new reservation (GiB) |
|---|---:|---:|---:|
| 95 | 11,972 | 202.3 | 209.6 |
| 61 | 55,496 | 211.2 | 262.7 |
| 337 | 91,068 | 380.5 | 390.0 |
| 62 | 91,620 | 256.5 | 390.0 |
| 139 | 96,048 | 248.3 | 390.0 |
| 265 | 126,527 | 380.6 | 390.0 |
| 140 | 187,668 | 383.4 | 424.1 |
| 266 | 314,195 | 454.9 | 578.5 |

These `peak` entries come from the executed query record's proving-memory
model, not an RSS sampler. Node resident samples during packing include both
slots and must not be attributed to a single proof. Cache hits are excluded.

The incident pair now reserves 635.0 GiB and cannot share a ~453 GiB node
budget. Small pairs still pack: 23,993 + 24,805 subjects reserve 449.6 GiB
together. Larger-than-node slots use the ordinary unpinned pool; admission
waits for that slot to finish before starting any neighbours, even when its
weight leaves room in the global budget. A concurrent calibration also raised
the mixed-pair reserve from 340 to 390 GiB (Mathlib predicted up to 385 GiB);
the Lean reference and scheduler diagnostics agree with that reserve. Proof
construction, claims and cache keys are unchanged.

This remains a calibrated scheduling estimate, not a hard RSS bound. The
recorded envelope covers this run through the 314,195-subject join; higher
joins and other workloads require checking against their completed records.
The running benchmark and its `IX_NUMA_PACK=0` setting were not changed.
