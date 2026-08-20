# Segment boundary control by grab-time admission

Status: **implemented and benchmarked** on `sb/aiur-planner` (`703940c`,
`crates/ffi/src/aiur/scan.rs`; model support in
`crates/aiur/src/synthesis.rs`). This document specifies the mechanism, the
invariants it does and does not provide, the measured results, and the
alternatives that were built and rejected — so a reviewer can attack the
design without re-deriving its history.

## 1. Problem

The prove-at-seal executor fills one shared `QueryRecord` with warm per-block
executions and periodically seals it as a segment, which is proven directly
(the record IS the witness). A sealed segment is only provable if its
predicted peak prove RSS — the padded analytic model
`AiurSystem::peak_prove_bytes`, validated at +3% — fits the box's acceptance
line (`PROVE_SEAL_FRAC × budget`).

Two facts make the boundary decision hard:

1. **A block's cost is unknowable before executing it.** Cost is dominated by
   definitional-equality reduction (delta-unfolding instantiated per block),
   which serialized size only weakly predicts. Regional GiB-per-static-byte
   varies 1.5–6× across one env (measured on FLT).
2. **The record is irreversible.** Multiplicities are shared, interleaved
   atomic counters with no per-block attribution, so an over-budget record
   cannot shed blocks; the only rollback is re-executing a shorter prefix
   into a fresh record ("trim-replay", ~30–60 s per occurrence).

Naive cutting — poll the metric, stop when it crosses a trigger line — made a
trim-replay the *routine* price of every seal in dense regions: by the time
the polled metric moves, 63 workers hold blocks that are already irrevocably
in flight. FLT's dense band degraded to ~3 blocks/s with multi-round trims.

The goal: segments that (a) seal under the acceptance line on the first try,
(b) execute at full worker parallelism with no barriers, and (c) cost no
tuned constants and no cross-environment fitted models.

## 2. Mechanism

### 2.1 Admission check (the primary boundary decision)

Before taking a block off the schedule cursor, a worker computes

```
projected_seal = metric_now + ratio × (inflight_static + next_block_static)
```

and refuses the grab (sets the segment-wide cut flag) when
`projected_seal ≥ acceptance_line`. Otherwise it grabs and executes.

The three inputs:

- **`metric_now`** — `peak_prove_bytes(record).peak`, the same padded model
  the seal will be judged by. Exact and cheap (~µs; a scan of per-circuit
  unique-query counters). No proxy gap between the control variable and the
  acceptance variable.

- **`ratio`** — the *marginal* density of the current region: metric bytes
  gained per serialized block byte completed, over the watcher's latest
  500 ms window, published as a fixed-point atomic
  (`Δpeak / Δstatic_bytes_completed`, ×2^16). Two deliberate properties:
  - *Marginal, never cumulative.* A segment's first blocks pull the whole
    shared dependency cone into the metric against a few KB of static bytes;
    a cumulative ratio (metric ÷ static-since-segment-start) overprices by
    roughly the worker count and seals worker-count-sized sliver segments
    (measured: 63-block segments, 38 segments for init). The cone lives in
    already-rolled-off windows; the marginal window prices only the region
    being executed now.
  - *Latest window, never smoothed.* See §5 for the two smoothing variants
    that measured worse.
  - A window in which nothing completed (a monster block mid-execution)
    publishes nothing; the previous ratio stands. Before the first window
    lands, admission degrades to `projected = metric_now` (the watcher
    backstop still guards the line).

- **`inflight_static` / `next_block_static`** — serialized block bytes from a
  prefix-sum over the schedule (built once at startup; any span's weight is
  one subtraction; in-flight = grabbed − completed, both O(1)). This is the
  input that makes the scheme *anticipatory*: serialized bytes are known
  before execution, and local aggregate size is a measured, strongly
  monotone proxy for regional record density (it ranked five probed FLT
  regions in exactly their measured cost order — where single-block max
  size and mutual-block flags both failed). A dense cluster therefore
  inflates the projection through its static weights while the metric is
  still flat — the case every purely metric-reactive scheme is structurally
  blind to.

Why grab time rather than a polling thread: the grab is the one moment a
worker consults shared state between blocks, so detection latency shrinks
from "up to 500 ms × 63 workers of progress" to "one block per worker" —
and the check is on the grab path, not the execution path, so it adds ~µs
against block executions of ≥10 ms.

### 2.2 What admission does NOT change

Everything below it is unchanged and remains the correctness story:

1. **Watcher backstop** (500 ms poll): cuts if the raw metric itself reaches
   the acceptance line — covers a ratio calibrated too low. Also records the
   trace (below) and publishes the ratio.
2. **Exact trace-trim** (rare): an over-line seal replays to the last watcher
   sample `(frontier, metric)` measured under the line. Every block below
   that contiguous completion frontier finished before the sample, so the
   replayed prefix's closure is a subset of what the sample measured — the
   reseal lands under the line *by construction*, in one round.
3. **Geometric descent** (rarer): if a reseal still lands over (the model is
   stepwise — circuit heights pad to powers of two — so a reseal can pin on
   a step), the next round's trim line drops by the observed overshoot,
   doubling per consecutive failure.
4. **UNPROVEN inventory**: a single block predicting over budget alone is
   executed, measured, reported, and excluded — never fatal.

Admission is therefore *advisory*: a wrong projection costs one exact trim,
never soundness, never a wrong witness.

## 3. Invariants and non-invariants

Provided:

- Sealed segments satisfy `peak_prove_bytes ≤ acceptance_line` (by admission
  in the common case; by trim-replay otherwise). Peak RSS during proving
  stayed under the cgroup cap in every benchmarked run.
- No tuned constants: the only configuration is the acceptance line itself
  (`PROVE_SEAL_FRAC = 0.95`, which is the RSS model's measured +3% validation
  tolerance, not a behavior knob). The ratio and the static weights are both
  measurements.
- No cross-environment model: nothing is fitted on one env and applied to
  another. The ratio is re-measured every 500 ms of the current run.

Explicitly NOT provided:

- **Zero trims.** Impossible in a single pass: block costs are unknowable
  pre-execution and the record cannot subtract. Trims are demoted to the
  rare cost of a mispredicted window (measured rates below), with an exact
  single-round recovery.
- **Full segments on high-variance envs.** The ratio's conservatism costs
  fill where density swings hard: FLT seals average ~60% of the line where
  init reaches ~95%. Two attempts to buy this back made other things worse
  (§5); the current position is that this is FLT's real variance, priced
  honestly.
- **A durable sizing guarantee ahead of execution.** A manifest-first
  "exact planner" alternative was analyzed and rejected for now: segment
  geometry depends on the boundaries themselves (each segment re-derives its
  shared tail from a fresh record), so an exact plan requires either
  executing candidate segmentations (which *is* online cutting) or per-query
  provenance capture — a per-entry attribution ledger on the hottest path in
  the system, plus record-pointer canonicalization, deferred as its own
  project.

## 4. Measured results

Dry runs (`--dry-run`: full cut/seal/trim geometry, no STARKs), one box,
64 vCPU / 495 GB, acceptance line 459.6 GiB:

| run | pure-metric grab check | admission |
|---|---|---|
| init (51,003 blocks) | 8 seg / 2+ trims | **7 seg / 0 trims / 3:27** |
| FLT 130k prefix | 45 trims, 59:32, killed unfinished at 123.6k | **13 trims, 35:42, complete** |
| FLT dense band (120.7k–125.2k) | ~3 blocks/s, multi-round trims | clean first-try seals, ~4 min |
| FLT 209.5k big-block cluster (800-block window) | 2 trims / 135 s | **0 trims / 69 s** |

Real end-to-end proving (execute + cut + seal + prove + verify, all proofs
verified, zero trim-replays in both):

| env | admission (`703940c`) | previous best | fleet baseline (prove-only, after a separate scan phase) |
|---|---|---|---|
| init | **23:45**, 8 segments | 25:16 | 31:48 |
| initstd | **40:07**, 13 segments | 48:38 | 55:40 |

Full-FLT dry inventory (in progress at time of writing): ~0.2 trims/segment
through the densest third, zero UNPROVEN blocks, the only skips being two
known Aiur/Rust kernel divergences (`MLListImpl` and its recursor —
unrelated to boundary control).

## 5. Alternatives built and rejected (measured, not argued)

1. **Cumulative-ratio admission** (first implementation): ratio =
   metric ÷ static-bytes-since-segment-start. The shared-cone head effect
   overprices by ~worker-count → 63-block sliver segments, init at 38
   segments. Replaced by the marginal window.
2. **5-window median ratio**: robust to spikes but lags density *ramps* by
   ~2 windows → late stops → init regressed from 0 trims to 8, wall 3:30 →
   8:03. Spike-robustness is worth less than ramp-latency costs.
3. **Padding-staircase reserve** (`peak + max_step ≥ line`, where
   `PeakProveBytes::max_step` is a sound bound on any single circuit's next
   power-of-two step): zero estimation, but simultaneously too blunt
   (always reserves the worst single step, ~130–165 GiB → seals at 252 GiB
   mean, +7% total BFFT, 76 vs 58 segments on the FLT prefix) and too weak
   (dense drains trip *multiple* circuits' steps → 7 residual trims).
   `max_step` remains in the model as an exact diagnostic quantity.
4. **Manifest-first exact planner** (two-pass; plan → cache → execute
   fixed ranges): see §3, deferred pending query-provenance work. Its two
   genuinely good ideas — padded phase-aware *work* accounting, and explicit
   `usable_RAM = cgroup − accounted-residency` replacing the 0.95 fraction —
   are adoptable incrementally and remain on the follow-up list.

## 6. Review questions worth asking

- The 500 ms watcher window is the one arbitrary-ish timescale left (it
  predates admission; chosen as "cheap to poll"). Admission inherits it as
  the ratio's window. Is there an argument for deriving it from worker
  count × typical block latency, or is it harmless?
- `ratio` is published by the watcher but consumed at grab granularity —
  a worker can act on a ratio up to 500 ms stale. The measured effect is the
  FLT fill gap; a per-grab incremental ratio (workers updating num/den
  atomically on completion) would halve staleness at the cost of two more
  hot-path atomics. Worth it, or is fill the wrong thing to optimize before
  padded-work accounting lands?
- The static prefix-sum uses serialized bytes. PR 550's `size^1.5` feature
  (superlinear typecheck cost in block size) is a plausibly better weight
  for the *in-flight* term specifically; it was not tried because the ratio
  denominates in plain bytes. A consistent ^1.5 variant is a contained
  experiment.
- Fill on high-variance envs: is ~60%-of-line acceptable long-term for
  FLT-class envs (more segments → more boundary re-derivation → the measured
  +5–8% execution overhead), or does that motivate the provenance/planner
  work earlier than otherwise?
