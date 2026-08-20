# Span-fleet execution: design

The whole-env proving engine behind `ix prove --env`: how one box turns
a serialized environment into a fleet of span proofs, and why it is
shaped the way it is. Code: `crates/ffi/src/aiur/scan.rs` (executor),
`Ix/Aiur/Stages/Codegen.lean` (kernel emit), `crates/aiur/src/trace.rs`
(debump/cancel). Measurements are from the 2026-08-20 campaign on a
32-physical/64-logical-core Xeon 6975P-C with 495 GB RAM, dry-run,
`IX_SCAN_RAM_GIB=400`, unless stated.

## The problem

Prove every constant of an env under `CheckEnv` claims, on one box,
where the env's total witness is orders of magnitude over any RAM
budget — so the work must be split into independently provable units —
and where the units' contents only exist at execution time, because a
record is the memoized trace of actually running the kernel.

Two prior shapes bracketed the design space:

- **Process fleet** (static shards, one process each): perfect
  isolation, but the work division is frozen before running — wall is
  the slowest shard — and RAM must be pre-partitioned per process
  (a 495 GB box could not run 32-wide on FLT: 29.4 GB x 32 does not
  fit, so half the cores sat idle for memory reasons).
- **Shared concurrent record** (all threads into one set-only record,
  multiplicities derived at seal): shares all memoization, but every
  count is derived by replaying the record, the shared structure is
  the scaling ceiling (init: 3.2x at 63 workers), and seal-time
  derivation serializes against execution.

The span fleet keeps the fleet's single-writer records and the
concurrent design's single process.

## Architecture

**One process, W workers, each owning a PRIVATE record.** A record has
exactly one writer for its entire life. Consequences:

- Multiplicities accumulate INLINE through the record's atomic cells
  (`fetch_add` on hit, insert-with-count on miss), exactly as the
  interpreter counts. Counts are exact at execution; there is no
  derivation pass. (Measured: the seal-time "fix" phase is 0.0s;
  under the shared record, derivation was a serialized replay of the
  whole record.)
- The codegen'd kernel emits accumulate semantics directly, including
  the promotion arm: a constrained hit on a zero-count entry replays
  the callee body constrained, activating its dependency tree — sound
  precisely because one thread owns the record.
- The executor's own per-block gauntlet calls are phantom consumptions;
  the seal DEBUMPS them, and roots the claim never consumed are
  retracted subtractively (`trace::cancel_dead_roots`). The result is
  byte-identical to a from-scratch derivation (kernel parity suite and
  all FFT pins pass unchanged).

**Min-cut schedule, contiguous grabs.** The env's blocks are ordered by
a hypergraph min-cut linearization (computed at prove time, ~4s on
init, ~60s on FLT) so closure-overlapping blocks are adjacent. Workers
claim contiguous granules (default 1024 blocks) off a shared cursor.
Contiguity is what confines cross-worker cone re-execution to range
boundaries: duplication is a boundary count, not a scatter. Measured on
init at 63 workers: granule 64 duplicates 61% of the FFT work, granule
1024 duplicates 9%.

**Range stealing for the endgame.** Block cost variance is real — the
min-cut order deliberately clusters heavy cones, and one granule can
hold a minute of serial work — so when the cursor drains, idle workers
STEAL: bisect the largest range still in progress. Owner and thief
serialize through one packed (next, hi) CAS per range: the owner claims
one block per CAS, the thief shrinks `hi`; no block is ever executed
twice or skipped. Boundaries (= duplication) are added only where the
schedule actually ran dry. Measured on init: no stealing 74.5s wall
with a 40s idle tail; stealing 50s wall at 1.22x duplication. A minimum
steal size bought nothing and cost 25s of tail (removed).

**Spans cut on retained bytes; workers seal their own spans.** When a
record crosses the cut threshold the worker seals it as a span — runs
the span's ONE canonical `CheckEnv` claim (owned-set root plus
thin-frontier assumption root, the same claim shape `ix verify` binds
to), debumps/cancels, and measures the exact witness peak — then starts
a fresh record. Sealing on the worker overlaps seal work with the other
workers' execution; a handoff pipeline to post-workers measured a 26s
post-only tail on init's 72s wall, because most workers' retained sits
under the cut and every span sealed after the schedule drained.

**Prove serialization behind a measured gate.** Dry-run needs no
pipeline at all — the worker measures and drops. In prove mode, sealed,
measured records ride one bounded channel to a single prove thread; it
pauses the workers (quiescent RAM baseline), re-checks the exact
measured peak against the prove budget, and refuses anything over it.

## RAM model

Two layers: conservative sizing for efficiency, an exact measured gate
for the guarantee.

- Budget = `MemAvailable` x (1 − 0.02), the residual being the
  measured gap between the analytic peak model and real proving
  (+1.6%/+1.7% on FLT/Mathlib campaign shards). `IX_SCAN_RAM_GIB`
  overrides.
- Cut = `min(0.02 x budget, budget/2/workers)` on retained bytes.
  Witness-to-retained measured 18–28x across campaigns, so 0.02 puts a
  span's witness near half the budget; the second term keeps all live
  records inside half the budget together.
- Prove gate: `peak_prove_bytes(record) <= budget − cut x workers`
  (execution never stops, so worker partials are pre-subtracted).
  Over-budget spans are REFUSED (`AIUR_SPAN_OVER_BUDGET`), never
  proven. Shards refuse identically (`AIUR_SHARD_OVER_BUDGET`) and a
  scheduler repartitions statically; claim composition makes any
  re-split sound.

Nothing is predicted and nothing adapts in-run: every prove decision is
a measurement of the sealed record at hand.

## What is shared, what is not

Shared, read-only: the env mmap, the decode cache, one `SharedIO` with
an env-canonical preassigned layout (all claims resolve io coordinates
against the same arenas). Not shared: records, and therefore
memoization across workers — traded away deliberately for exact inline
counts, at the measured price of boundary duplication (init 1.22x,
FLT 1.41x against ideal FFT).

## Where it stands (2026-08-20, dry-run)

| env | span fleet | old shared record | branch fleet | main fleet |
|---|---|---|---|---|
| init wall / cpu | **50s / 1.9k** | 71s / 3.1k | 54s / 2.6k | 34s / 0.9k |
| FLT wall / cpu | **~1800s* / 62k** | 1999s / 88.6k | 2171s / 63.5k (16-way) | 1802s / 26.9k (16-way) |

\* 99.9% coverage on the pre-fix kernel: one monster block ran serially
past 33 minutes and was killed (below). Main fleet's init advantage is
its per-process isolation amortized over a shallow env; its FLT number
is bounded by RAM pre-partitioning (32-way does not fit the box).

## Known limits

- **Monster blocks.** Stealing is block-granular; a single
  `verify_block` whose cone approaches the box is serial, unstealable,
  and can overshoot the cut arbitrarily (cut checks run between
  blocks). The shared record masked such blocks by having their cones
  collectively warm. Upstream kernel work (struct-eta scoping, Int
  primitives, projection def-eq) targets the known offenders; if a
  class of them survives, the answer is monster-aware handling — a
  planner pre-pass or deferral to the shard path — not executor
  heuristics.
- **Cone-to-cut ratio.** Duplication scales with span boundaries; envs
  whose shared cones are large relative to the cut pay more (FLT 1.41x
  vs init 1.22x). Bigger cuts amortize better but are capped by the
  witness-to-retained ratio against the budget.
- **One address space.** An OOM or runaway block threatens the whole
  run; a fleet loses one shard. The branch keeps static shards as the
  cluster unit for exactly this reason — the span fleet is the
  single-box engine.
