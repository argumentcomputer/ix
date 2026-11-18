# Prover resource defaults

`ix prove --ixe ENV.ixe`, with no other flags, should prove any environment
on any supported machine without leaving the hardware idle and without
exceeding host or device memory. The supported machines range from a
CPU-only host to multi-GPU hosts such as the g7e family (one, two or four
96 GB RTX PRO 6000 cards). This document derives every sizing decision from
the machine instead of from flags, and states which bounds are enforced at
run time and which rest on calibrated estimates.

## 1. Problem

Proving an environment takes two sizing decisions: how much of the
environment one claim covers (env sharding) and how much of one claim's
execution one proof covers (trace sharding). Today these decisions are
spread over flags and constants that must agree across commands:

| Setting | Where | What goes wrong |
|---|---|---|
| `ix shard --max-ram G --exec-jobs N` | partition | Required, no default. The shard count depends on the *later* `ix prove` flags; different guesses give different partitions (Init: 3 shards at 180 GiB / 2 jobs, 4 at 201 GiB / 3 jobs). |
| `ix prove --max-ram` | controller | Per GPU with `--lanes`, total with `--jobs`; `ix shard --max-ram` is per shard. Three meanings. |
| `ix prove --exec-jobs` | controller | Default 0 means "all cores", so one lane admits 32 concurrent executions; the record pool then serializes them. |
| `--lanes` | controller | Lane *i* runs on device *i*; one GPU with two lanes fails unless `IX_PROVER_SHARED_DEVICES=1`. `bench-ixvm` hard-codes two lanes. |
| `AIUR_RECORD_MAX_BYTES` | controller | 128 GiB regardless of host. |
| `AIUR_TRACE_SHARD_MAX_CELLS` | planner | 1.5·10⁹, sized for one 96 GB card at `log_blowup = 2`; not read from the device. |
| `AIUR_HOST_WORKSPACE_BYTES` | controller | Derived from the cell constant, not from the host. |
| plan-fit errors | planner | Report the host workspace even when the failed constraint is device memory or the cell cap. |
| `AIUR_GPU_TRACE` | planner | Declines device population silently when the device record does not fit. |
| `--binding-proof` | controller | Manual; whether it pays depends on the claim count. |
| one-shard manifests | controller | Rejected (`lanes.rs`: "the manifest has one shard; there is nothing to join"). |

Correct runs require knowing the internals, and an incorrect guess is
indistinguishable from a regression.

## 2. Principles

1. **Detect, then derive.** The machine reports its total host memory,
   cores, GPUs and device memory. Every budget is a function of those
   numbers, so the same machine always derives the same budgets. Limits
   imposed from outside (cgroups) are the harness's concern, not the
   prover's (§3.1).
2. **One owner per decision.** Trace sharding is decided per proof by the
   planner. Env sharding is decided once, by the controller. Both read the
   same joint sizing (§4); no command needs another command's flags.
3. **Enforce what can be enforced; calibrate and verify the rest.** Record
   memory is enforced at run time by measured reservations. Prover
   workspaces and device peaks are planned from a model; they are bounded
   by the model's calibration and checked in CI against measured peaks
   (§5.3). The document does not claim more.
4. **Estimates are conservative and library-agnostic.** The env-sharding
   model is calibrated on Mathlib, the largest and most varied library
   proven, and biased to over-predict. No per-library state is cached:
   benchmarking many libraries must not depend on having seen them before.
5. **Flags are overrides, not requirements.** Every current flag and
   environment variable keeps working and takes precedence; none is needed.
6. **Say what was derived and what failed.** The controller prints its
   derived budgets on start, and every refusal names the constraint and the
   values that violated it.

## 3. Resources

| Symbol | Meaning | Source |
|---|---|---|
| H | host memory: `MemTotal` | §3.1 |
| C | usable cores | `sched_getaffinity` |
| G | GPUs | devices visible to CUDA (`CUDA_VISIBLE_DEVICES`) with a compatible kernel image; 0 in a CPU build or on a host without one |
| D | device memory per GPU | `cudaMemGetInfo` free memory of each device at start |

A CUDA build on a host without a GPU behaves as a CPU build. Heterogeneous
GPUs use the smallest D.

### 3.1 Host memory

H is the machine's capacity, `MemTotal`, and nothing else. The prover reads
neither `MemAvailable` nor any cgroup limit:

- **Reproducible sizing.** `MemAvailable` changes with page cache, tmpfs and
  whatever else is resident at that moment, so sizing from it gives a
  different partition for the same environment on the same machine from run
  to run.
- **A cap is the caller's decision.** A benchmark harness or CI job that
  wants to bound the prover sets a cgroup limit outside the process and
  passes the matching `--max-ram`. The cgroup then turns an overrun into a
  reported OOM of that process, not a host hang.

So the defaults assume the prover has the machine to itself.
`--max-ram` is the only way to plan for less.

## 4. Joint sizing

Host and device constraints interact: a larger trace shard needs a larger
per-lane prover workspace, which leaves less host memory for records. The
controller therefore sizes both together, once, at start.

Inputs: `H`, `C`, `G`, `D`, the measured resident bytes `R` after the lanes'
programs, environment and keys are loaded, and two monotone models from the
planner:

- `W(c)`: host workspace of a lane proving trace shards of `c` committed
  cells (the planner's peak model, `aiur-trace-sharding.md` §7.3);
- `Dev(c)`: device peak of such a shard (§7.1 of the same document).

Procedure:

1. **Host budget.** `B = 0.8 · H − R`: one 20% reservation in total, which
   covers allocator pages, transient buffers and the operating system. No
   other factor discounts `H`; the record pool and the lanes' workspaces
   are both carved out of `B`.
2. **Lanes.** `L = G`, one per visible GPU (counted from the driver's
   device entries and `CUDA_VISIBLE_DEVICES`, without initializing CUDA);
   on a CPU host, `L = 1` with all cores. Each lane gets the available
   cores as executor threads (`--exec-jobs` caps them), but memory, not the
   thread count, decides how many execute at once (§5.5): up to the `E` of
   step 5 start as before, and more only while their predicted records fit.
   Starting executions without regard to their records does not help: a
   started execution holds a growing record, so on Mathlib (records of
   35–60 GiB) 32 concurrent executions stalled each other in the 194 GiB
   pool, finished one at a time about every 2.5 minutes, and 10 were
   cancelled and requeued, discarding their work.
3. **Cell ceiling from the device.** On a GPU host,
   `c_dev = max{c : Dev(c) ≤ 0.85 · D}`. On a CPU host, `c_dev = ∞`.
4. **Record floor.** `r_min` is the largest predicted record of any atomic
   block in the environment (§5.1), and at least a fixed floor (8 GiB). The
   pool must hold one such record.
5. **Records held.** The partition is sized so that
   `n = E + 2L` records fit at once: `E = 3G` executing (one on a CPU host)
   plus, per lane, one in the prepared queue and one being proven (the
   controller's admission slots). Each execution is a single-threaded run
   whose record is tens of GiB, so memory, not cores, limits how many run
   at once, and execution is usually what the GPU waits for. The Init root
   (one GPU, 4 claims of 28–30 GiB, 473 s) left the GPU idle for about
   150 s: 105 s until the first claim had executed, then 17 s and 28 s
   while join and root executions that depended on finished proofs ran.
   Keeping one GPU busy needs about 1.9 executions at once on Init: claim
   and join execution (about 105 s and 50 s) against their proofs (about
   52 s and 30 s). Executions running together are 12–18% slower than alone
   (92 s alone against 105–109 s with four), so `E = 3G` leaves headroom; a
   Mathlib claim record (54 GiB) also exceeded a share sized for `2G`.
   The Mathlib run is to check it (§9.2). `E` is the one tuning constant
   (`EXECUTIONS_PER_GPU` in `crates/ixon/src/shard.rs`), and it is a floor
   of admission, not a cap: claims predicted lighter than `s` run more at
   once (§5.5).
6. **Cell size.** Choose the largest `c ≤ c_dev` with
   `B − lanes · W(c) ≥ n · r_min`. On a CPU host this also bounds `c` from
   above through `W`; there `c` is additionally capped so that
   `lanes · W(c) ≤ B / 2`, leaving at least half of the budget to records.
7. **Degrade before refusing.** If no `c` satisfies step 6, reduce `n`
   toward 1, then reduce `c` toward the smallest cell size the planner
   supports (`c_min`, the size below which recursive verification work
   dominates). If `B − lanes · W(c_min) < r_min` still, refuse and report
   the floor: "this environment needs a budget of at least
   `R + W(c_min) + r_min`; `0.8 · H` is `B + R`".
8. **Results.** Shard cell limit `c`, workspace `W = W(c)`, record pool
   `P = B − L · W`, records held `n`, record share `s = (0.8 · H − L · W) / n`.
   `ix shard` and the controller both call `record_share`
   (`crates/ixon/src/shard.rs`) with the same budget, workspace and GPU
   count, so with no flags `ix shard` seeds the partition `ix prove` is
   sized for. The share leaves `R` out on both sides, as `ix shard` loads
   no prover; the controller's pool does subtract it.

The controller prints the inputs and results in one line, for example:

```
[resources] H 249.0 GiB total, C 32, G 1 × 95.1 GiB free → budget 199.2
  (20% reserved), resident 2.0, cells 1.5e9, workspace 24.2 GiB/lane,
  record pool 173.0 GiB, 5 records held, share 34.6 GiB
```

With no flags, every one of these is derived. `--max-ram` overrides
`0.8 · H` (and so `B`), `c` replaces `AIUR_TRACE_SHARD_MAX_CELLS`, `W`
replaces `AIUR_HOST_WORKSPACE_BYTES`, `L` replaces `--lanes`, and `E`
is set by the one constant `EXECUTIONS_PER_GPU`; `--exec-jobs` only caps the
executor threads (§5.5).

### 4.1 Devices shared by lanes

By default every lane has its own device, and the planner plans each proof
against that device's budget. More lanes than GPUs happen only on request
(`--lanes`). Then each device has one device budget, and proving rounds on
it reserve their planned device peak from that budget before starting; a
round whose peak does not fit waits for the device. Executions, which use
host memory only, still overlap. With this per-device admission,
`IX_PROVER_SHARED_DEVICES` is implied by `lanes > G` and no longer needed.

`bench-ixvm` requests `min(claims, max(G, 1))` lanes.

## 5. Env sharding

### 5.1 The record model

A claim's peak host memory is its execution record. Across the libraries
measured so far the record is close to linear in the serialized bytes of the
blocks the claim owns: Mathlib's ordinary shards average about 1,700 record
bytes per serialized byte (18.8 MB of blocks, 29.3 GiB records), and Anthropic
FLT's single-constant outliers fall on the same line (58.5 MB, 89.5 GiB;
`gpu_seed_shards` in `crates/ixon/src/shard.rs`). Init's 3-shard partition
measured 38.6–42.9 GiB per claim.

The model predicts a claim's record from its actual cut
(`predicted_record_bytes` in `crates/ixon/src/shard.rs`, the one function
both the shard-count seed and the controller's admission use):

```
record(S) = α · Σ_{b ∈ S} size(b)   +   β · frontier_bytes(S)
```

- `α ≈ 2,362` record bytes per owned byte is the seed's calibration: the
  41.4 GiB reference share over the reference shard's owned bytes
  (`41.4 GiB × 78 / 1,468,041,216 B`). A shard owning the reference's bytes
  per shard is predicted at exactly the share it was seeded for.
- `β = α / 3`, the frontier term: least squares of `record − α · owned`
  against frontier bytes over the 74 claims of two measured Mathlib runs
  (55 claims on 2026-11-04, 19 on 2026-11-16) gives 786 bytes per frontier
  byte (889 and 463 per run). Frontier blocks are hashed and parsed, not
  typechecked, so they cost less record than owned bytes.

On those 74 claims the model's measured/predicted ratio has median 0.97,
p90 1.24 and maximum 1.72 (owned bytes alone: 1.12, 1.38, 2.04). The seed
predicts before any cut exists, so it uses the owned term alone; the
frontier term is why a seeded shard's prediction is about 15% above `s` on
Mathlib. Admission absorbs the spread (§5.5); an over-prediction costs some
concurrency, an under-prediction an overshoot, and only a record over the
ceiling a bisection (§5.4).

A block is **atomic** when its own predicted record exceeds `s`: it cannot
share a shard and is proven alone, as a batch of trace shards, on the
exclusive path (§5.4).

### 5.2 Partitioning under the record bound

The bound "every ordinary shard's predicted record is at most `s`" is a hard
constraint, and equal predicted FFT cost is only the objective. The FFT
model and the record model differ, and frontier bytes depend on the cuts, so
a shard count alone cannot enforce the bound. The partitioner therefore:

1. Isolates atomic blocks.
2. Seeds the count at `ceil(Σ record(b) / s)` over the remaining blocks and
   cuts with today's static strategy (min-cut over walk-edge nets, then
   rebalance toward equal predicted FFT cost, `STATIC_OWNED_PER_BYTE`).
3. **Validates** every shard against the bound using its actual cut,
   frontier included.
4. **Refines** each violating shard by bisecting it with the same min-cut
   (the frontier of the halves is recomputed), and repeats from step 3. A
   shard that cannot be bisected below `s` without isolating a single block
   has its heaviest block marked atomic.
5. Rebalances FFT cost only through moves that keep both shards within `s`.

The loop terminates because every refinement strictly reduces the largest
violating shard. `ix shard` runs the same procedure from the same derived
`s`, so its output is the partition `ix prove` would use.

Dispatch is in decreasing predicted record size, joins before claims, so the
run does not end on a heavy leaf with the other lanes idle.

### 5.3 What is enforced and what is estimated

| Memory | Bound | Mechanism | If wrong |
|---|---|---|---|
| Execution records | enforced | Each execution is admitted against its predicted record (§5.5), reserves its record's bytes from `P` as the record grows, and waits for capacity when the pool is full; when every execution waits and nothing drains, the youngest is cancelled and retried. | A record that outgrows its prediction grows into the overshoot buffer, waits, or is bisected (§5.4); it cannot exceed `P`. |
| Prover workspace (host) | estimated | The planner's peak model (`planning.rs`: "an estimate, not an allocator limit"), checked by `W(c)` in §4. | Not bisectable at run time. |
| Device peak | estimated | The planner's device model against the per-device budget (§4.1). | Not bisectable at run time. |
| Everything else | estimated | `R` is measured at start; the 20% reservation covers allocator pages, transient buffers and the operating system. | — |

For the estimated rows the bound is only as good as the model, so the
design treats the model as a calibrated artifact:

- `W(c)` and `Dev(c)` carry their own safety factor, fitted from measured
  peaks (process peak RSS from the lane log, device peak from multi-stark's
  allocation statistics) on a fixed set of proofs.
- A CI job proves a fixed Init partition on CPU and on one GPU and fails
  when a measured peak exceeds its planned peak, so a prover change that
  grows workspaces cannot silently invalidate the defaults.
- Benchmark and CI harnesses run the prover under a cgroup memory limit,
  set outside the process, so an underestimate there becomes a reported
  OOM of the measured process (`benchmarking.md`, OOM rows), not a host
  hang. The prover itself does not read that limit.

Making the workspace an enforced bound (a tracking allocator that reserves
from the same pool, so an underestimate waits or fails cleanly) is a
separate change, listed in §9.

### 5.4 Ceilings and the exclusive path

Two kinds of work have different record ceilings:

- **Ordinary claims** have ceiling `min(P, 2s)`. A claim whose record
  exceeds it is stopped, its leaf bisected and the partition checkpointed
  (`aiur-gpu-proving.md` §3), so a mis-predicted claim is split early
  instead of holding the pool.
- **Unsplittable work** — atomic-block claims, aggregation records (joins
  and the root, which `lanes.rs` cannot split today) and the compression
  root wrap — runs on an **exclusive path**: the controller stops admitting
  new executions, waits for the pool to drain to the in-flight proofs'
  needs, and runs the unsplittable execution with ceiling `P` alone. Its
  proof is planned as a batch of trace shards like any other.

When unsplittable work exceeds `P`, the controller refuses with the
record's measured size, `P`, and the host memory a run would need (§4,
step 7). It does not bisect it.

### 5.5 Admission by predicted record

The controller (`crates/aggregate-controller/src/lanes.rs`, with the
accounting in `record_pool::Ledger`) starts an execution only when the
record pool admits it. Executor threads never take work speculatively.

**Charges.** A claim is charged its predicted record: the record a
previous run measured, when the manifest carries one (below), otherwise the
model of §5.1. The run does not rescale the model from the claims it has
measured: claims of one library differ in kind (nested unfolding,
recursion, `Nat` arithmetic), so early claims say little about later ones,
and the overshoot buffer, freezing and cancellation absorb the error
instead. A join or the root is charged the larger of its two inputs'
records when both were measured in this run, otherwise the largest
aggregation record measured so far, or 44 GiB before any is known (every
one of the 54 aggregation records of the 2026-11-04 Mathlib run was at most
43.4 GiB). On that run the larger input fell short 3 times, by at most
9.2 GiB (the root, 32.2 GiB, over inputs of 23.0 and 22.6 GiB), well within
the buffer, while charging the largest aggregation so far overcharged the
median aggregation by 1.6x.

**Admission.** Up to `E = 3G` busy executor threads (step 5 of §4; a thread
is busy until the prepared queue takes its record), an execution is
admitted as the fixed policy admitted it: whenever one share `s` is free
and no execution holds growth priority. Beyond that it is admitted only
while admission is not frozen and

```
Σ running charges  +  executed records awaiting or in proof  +  charge  +  s  ≤  P
```

where a running execution counts its charge or its grant, whichever is
larger. The last `s` is the overshoot buffer, kept unpromised. With nothing
executing an execution is admitted whatever its charge, so a record larger
than the free pool still runs alone. Joins keep their priority: a ready join that
does not fit holds back the claims behind it. Root wraps and the binding
discharge, which run once nothing else executes, are admitted by the
fixed rule with one share up front.

**Overshoot.** An execution grows freely up to one buffer past its charge.
Further growth contends: it waits for the execution holding growth priority
(the oldest waiter, until it finishes) and never takes capacity other
running executions were admitted for and have not grown into. While the
running executions exceed their charges by more than the buffer, and from
the moment they do or one waits to until an execution finishes, admission
beyond `E` is frozen; a proven record draining does not reopen it. When
every execution waits, no executed record is draining, and the priority
holder cannot grow, the youngest other execution is cancelled and requeued
(the existing rule). A record over the ceiling is bisected (§5.4).

**Guarantees.** Admission never runs fewer executions than the fixed policy
would: up to `E` it is the fixed policy. With accurate predictions it never
freezes or cancels: running charges and the buffer fit `P`, and growth that
meets a record awaiting proof waits for the GPU to drain it. A single
execution overshooting by up to `s` grows into the buffer without a freeze
or a cancellation. The worst case is correlated overshoot: many claims
admitted on light predictions that all turn out heavy. Each claim is
charged by its own prediction, never by what other claims measured, so
when every claim of a run is four times heavier than predicted, the pool
fills, executions that cannot grow are cancelled and rerun, and in
simulation the run finishes 2.7% later than the fixed policy. After a
stretch of accurate claims the same error costs nothing: the run finishes
2.4% sooner, with no cancellations.

**Learning.** Each executed claim's record is written into the partition
`--out-ixes` saves (the `.ixes` measured-records section: presence byte,
then one `u64` per shard, `0` = unmeasured; written only when some claim
was measured, so manifests without measurements keep the earlier layout).
Rerunning on that partition admits those claims by their measured size.
Bisection keeps the measurement of every shard it does not split.

**Simulation** (`crates/aggregate-controller/src/tests/admission.rs`: one
GPU, the 2026-11-16 Mathlib host's 194 GiB pool and 40.1 GiB share,
execution 3.6 s and proof 1.8 s per GiB of record as measured on Init,
4% slowdown per further running execution; claims only). Against the fixed
policy on the same claims:

| Claims | Finish (fixed → predicted) | Most at once | Cancelled (executor-s) |
|---|---|---|---|
| 24 accurate, 34–46 GiB | 1873 s → 1878 s | 3 → 4 | 0 → 0 |
| 55 Mathlib claims as measured on 2026-11-04 | 5715 s → 5650 s | 3 → 3 | 0 → 0 |
| 64 light (`s/4`), GPU-bound | 1256 s → 1274 s | 3 → 15 | 0 → 0 |
| 64 light, execution twice as slow per byte | 1731 s → 1330 s | 3 → 15 | 0 → 0 |
| alternating 10 and 60 GiB | 2345 s → 2236 s | 3 → 5 | 0 → 0 |
| one claim 15 → 45 GiB (3×, within the buffer) | 1883 s → 1888 s | 3 → 4 | 0 → 0 |
| one claim 40 → 80 GiB, 12 placements summed | 23475 s → 23568 s | — | 0 → 0 |
| one claim 40 → 120 GiB, 12 placements summed | 26322 s → 24918 s | — | 3 (579) → 0 |
| one claim 40 → 200 GiB (over the ceiling), 12 placements summed | 31658 s → 30012 s | — | 7 (1413) → 0 |
| 24 claims 10 → 40 GiB (whole run 4× heavy) | 1885 s → 1935 s | 3 → 15 | 0 → 11 (1334) |
| 16 accurate 10 GiB, then 32 at 10 → 40 GiB | 2716 s → 2650 s | 3 → 15 | 0 → 0 |

Where the GPU is the bottleneck (accurate claims, light GPU-bound claims,
a single 2× or 3× claim) the two policies finish within 1.4% of each other:
the extra executions only contend for the cores. The whole-run 4× error is
the one row with cancellations.

**Log.** At dispatch, each claim's predicted record, its basis (measured,
or model; for a join, its larger input, the largest aggregation so far,
or the aggregation default) and its charge; at completion, its
record against the prediction; and at the end one `admission:` line with
the measured/predicted distribution (as admitted and for the model alone),
how many claims overshot and by more than `s`, the most executions at once,
how often and how long admission was frozen, and the cancellations with
the executor-seconds they discarded.

## 6. Proofs that cannot be trace-sharded

Some proofs must be a single trace shard at fixed heights, the compression
root wrap in particular. When such a proof's device peak exceeds the device
budget:

1. If its host peak fits `B`, the CUDA build plans it on the host and says
   so. The device stays available for the stages that fit.
2. Otherwise the refusal states the device peak, the device budget, the
   host peak and the host budget.

The planner's fit test reports which constraint failed: host peak against
host budget, shard cells against the cell limit, or device peak against the
device budget.

For example, the Init root wrap at a headroom-0 layout needs 110 GB of device
memory, and 261 GB of host memory at the release layout (headroom 1). On a
single-GPU host with 249 GB of RAM neither fits at headroom 1; at headroom 0
the host path fits (80 GB peak), and `ix compress` reuses a root normalized
into its output directory, so a CPU build can normalize and a CUDA build
compress.

## 7. One-shard environments

The partition legitimately has one shard when the environment is small or
the machine large. That claim, `CheckEnv(env root, none)`, already states
the whole environment with no assumptions, so the controller proves it and
returns its proof as the root, with no join. `ix verify --aggregate`
accepts a root that is a single claim proof, checking that its subjects are
exactly the environment's constants in Lean's logic, as it does for joins
(`auditAggregateConstants`). Compression normalizes such a root like any
other.

## 8. Choices made automatically

| Choice | Default | Basis |
|---|---|---|
| Binding proof | Proven once per binding and assumed by every claim when the partition has at least `k` claims | Each claim saves its role validation; the root pays one discharge. On Init with 3 claims the two cancel (516 s without, 525 s with, plus 50 s to prove the binding). `k` is calibrated with the record model. |
| Device trace population | `compiled` when compiled writers are registered, else `generated`, else host | Unchanged; the planner logs, per proof, how many circuits it populated on the device and why the others stayed on the host. |
| Retention | `auto` | Unchanged. |

## 9. Rollout

Each step is independently useful and keeps the current flags working.

**Done.** The host budget is `0.8 · MemTotal` with no other reservation and
no cgroup or `MemAvailable` read (§3.1, §4 step 1); `--max-ram` is the
whole-process budget in every command; `ix shard` needs no flags and seeds
from the same budget, GPU count and records held as `ix prove` (§4 steps 2
and 5, without the record model of §5.1); `ix prove --aggregate` and
`--compress` default to one lane per visible GPU.

1. **Derive and report.** Resources per §3.1, the joint sizing of §4 with
   its `[resources]` line and refusal floors, `bench-ixvm` lanes, and
   plan-fit errors that name the failed constraint.
2. **Admission.** Executions gated by the pool alone; a dispatch order
   once §9.2 has the data to choose one; ordinary and exclusive ceilings (§5.4); per-device admission
   for shared devices (§4.1), after which `IX_PROVER_SHARED_DEVICES` is
   implied.
3. **One-shard roots** (§7).
4. **The record model and partitioner.** Calibrate `α`, `β` on Mathlib;
   the validate-and-refine partitioner of §5.2; the CI checks of §5.3.
5. **Optional manifest.** `ix prove --ixe` partitions with the same
   derivation; `--ixes` remains for pinned partitions.
6. **Host fallback for proofs that cannot be trace-sharded** (§6) and the
   automatic binding proof (§8).
7. **Enforced workspaces.** A tracking allocator for prover workspaces that
   reserves from the host pool, turning the estimated rows of §5.3 into
   enforced ones.

### 9.1 Calibration

The record constants are calibrated on Mathlib, with provenance recorded
beside them as today:

1. Shard Mathlib at three record shares spanning the supported machines.
2. Execute every shard without proving (`ix prove --exec-only`) and record
   `(owned bytes, frontier bytes, record bytes)`.
3. Fit `α`, `β` by least squares, then raise them to the p99 of the observed
   ratio.
4. Validate out of sample on Init, Std, ISLB and FLT: no shard's measured
   record may exceed its prediction by more than the margin.

The record depends on the IxVM program, not on the library: recalibrate when
IxVM changes. A CI check compares the measured records of a fixed Init
partition with the model and fails when the model under-predicts beyond the
margin.

### 9.2 Open: uneven work across shards

Shards the partitioner balances by predicted cost can differ widely in
actual typechecking work, so their records and execution times differ too.
That decides two choices this document leaves open:

- **Dispatch order.** A heavy claim dispatched first lengthens the GPU's
  initial idle time; dispatched last, it lengthens the tail. Ordering only
  helps as far as the work can be predicted before execution, which the
  static model does not do for typechecking cost.
- **Shard size.** `E = 3G` and the share `s` assume claims of similar
  weight. Admission by predicted record (§5.5) lets lighter claims run more
  at once and holds heavier ones to their memory, but it is only as good
  as the record model, and heavy-for-their-size claims still make the
  overshoot buffer, waits and bisections carry more of the load.

The Mathlib run records, per claim, the predicted and measured record,
execution and proving time, and when the GPU waited, and ends with the
`admission:` summary (§5.5), to measure the spread and find what predicts
it.

## 10. Flags after the change

| Flag or variable | Status |
|---|---|
| `ix prove --max-ram`, `ix shard --max-ram` | Override for `0.8 · H`, the whole-process host budget across all lanes, in GiB; the same meaning in both commands. A harness that caps the prover's cgroup passes its cap here. |
| `ix prove --exec-jobs` | Optional cap on executor threads per lane (default 0: the cores divided among the lanes). Admission by predicted record decides how many execute (§5.5); there is nothing to tune. |
| `ix prove --lanes`, `--jobs` | Override for the lane count (default: one per visible GPU). `--jobs` proves on CPU lanes even when GPUs are present; more lanes than GPUs share devices under per-device admission. |
| `ix prove --ixes` | Optional: prove a fixed partition instead of the derived one. |
| `ix shard` | Needs no flags: it derives the partition `ix prove` would, so its output can be inspected or pinned. `--shards N` fixes the count. |
| `ix shard --exec-jobs` | Removed: the records held are derived from the GPU count (§4, step 5). |
| `RAM_USABLE_FRAC` (0.85 of `MemAvailable`) | Removed, with the controller's separate 10% headroom: the single reservation of §4 replaces both. |
| `cgroup_memory_limit` in the controller | Removed: the prover does not read cgroup limits (§3.1). |
| `AIUR_TRACE_SHARD_MAX_CELLS` | Override for `c`. |
| `AIUR_HOST_WORKSPACE_BYTES` | Override for `W`. |
| `AIUR_RECORD_MAX_BYTES` | Override for the ordinary ceiling. |
| `IX_PROVER_SHARED_DEVICES` | Removed: implied when lanes exceed GPUs. |

`ix prove --plan-only` prints the resources, the joint sizing, and the
partition (count, predicted records, atomic blocks, dispatch order) without
executing.

## 11. Expected defaults

For a host with `G` 96 GB GPUs, `H` total, the 20% reservation and the
1.5·10⁹-cell shards a 96 GB card admits (`W` ≈ 24 GiB per lane), ignoring
`R`:

| G | H | lanes | records held `n` | record pool `P` | record share `s` |
|---|---|---|---|---|---|
| 1 | 249 GiB | 1 | 5 | ≈ 175 GiB | ≈ 35 GiB |
| 2 | 480 GiB | 2 | 10 | ≈ 336 GiB | ≈ 34 GiB |
| 4 | 980 GiB | 4 | 20 | ≈ 687 GiB | ≈ 34 GiB |
| 0 | 480 GiB | 1 | 3 | ≤ 192 GiB (half of `B` reserved for `W`) | ≤ 64 GiB |

On the CPU-only host the prover workspace, not the record, bounds the claim.

## 12. Acceptance

On each machine shape (CPU-only, 1, 2 and 4 GPUs), `ix prove --ixe` with no
flags, on a single-constant environment (one shard), Init, ISLB and Mathlib:

- completes, with no process killed by the cgroup and no device OOM;
- on the measured process, peak RSS and device peak stay within their
  planned values;
- performs at most one bisection per thousand claims;
- keeps each GPU busy at least 70% of the proving phase (sampled with
  `nvidia-smi`), after the first claim's execution;
- prints the `[resources]` line and, for every bisection or exclusive
  execution, the prediction it corrected;
- refuses, with the stated floor, on a host whose memory is below it.
