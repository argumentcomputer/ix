# Handoff: recursion FRI-parameter bench + metal-48xl proving plan

Two related work items: (1) the FRI-parameter hypothesis and the bench
that settles it; (2) the single-box r8i.metal-48xl plan for the full
Mathlib prove+aggregate run, which consumes (1)'s outcome as its
Stage 2 multiplier.

# Part 1: recursion FRI-parameter hypothesis + bench to run

Decision at stake: whether the `ix_aggr` recursion layer (Stage 2
wraps/joins) should move off `logBlowup=2, numQueries=100, PoW=20`
toward fewer queries, and whether raising `logBlowup` to 3 (rate 1/8,
the SP1 shrink/wrap and zisk-recursion posture) helps or hurts. Stage 2
cost is `(2N−1) × per-slot cost` and per-slot cost is dominated by
verifying child proofs in-circuit, which scales with the *child's*
query count — so this parameter choice is the single biggest lever on
aggregate wall clock and per-slot RAM.

## Current state

- Production params (both layers identical today):
  `Ix/Aiur/Protocol.lean` `defaultCommitmentParameters` (logBlowup 2,
  capHeight 0) + `defaultFriParameters` (q=100, queryPoW 20, PoW-commit
  0, maxLogArity 1, finalPolyLen 0). Recursion clones them via
  `Ix/MultiStark.lean` `defaultRecursionParameters` (deliberately a
  separate knob).
- CI recursion bench params: `Benchmarks/Typecheck.lean`
  `recursiveFriParameters` = **q=50, logBlowup 2, PoW 0** — chosen for
  the CI host's RAM ceiling. In `--recursive` mode the WHOLE system
  (inner IxVM prove + outer verifier prove) runs under these.
- Field is Goldilocks, challenges in the quadratic extension (~2^128).
  On the ethSTARK-conjecture scale (`log_blowup·q + queryPoW`):
  production = 220 bits, CI bench = exactly 100 bits. Under proven
  bounds production is ~100–120-bit-class; q=50 is ~70 (Johnson) /
  ~54 (unique-decoding). Which regime to target is a separate policy
  decision — the bench below is an equal-*conjectured*-bits comparison
  for performance only, not a security sign-off.

## Measured baselines

- Production Mathlib Stage 2 (q=100 both layers, PR #598 / PROVENANCE
  in `Tests/Fixtures/Aggregate/mathlib-2026-09-03/`): 477 slots in
  14:46 wall at `--jobs 2` ≈ ~110 s/slot serialized, per-slot peaks
  ~245 GiB (491 GiB RSS at 2 jobs), wraps ~101 s / 187–196 GiB at Init
  scale, proofs 8–9.5 MiB.
- CI bench at q=50 (PR #605 comment
  https://github.com/argumentcomputer/ix/pull/605#issuecomment-5514660144,
  "FRI verifier on FRI" table = the wrap-shaped workload): verifier
  prove 18–31 s, peak 59–102 GiB (single-constant scale), proof
  ~4.0 MiB. Everything ~halves vs the q=100 shape, consistent with
  cost ∝ child queries.

## Hypotheses

**H1 (query lever — corroborated, quantify at scale).** Recursion cost
per slot (time AND RAM) scales ~linearly with the child's query count.
q 100→50 ⇒ Stage 2 ~13–15 serialized box-hours → ~7–8, per-slot peak
~245 → ~120–150 GiB (which would admit 3 slots per 512 GiB box).

**H2 (blowup 3 loses in the tree layer).** At equal conjectured bits,
`q ∝ 1/log_blowup` but prover commit cost and RAM ∝ trace·2^b, so
steady-state per-node cost ∝ (witness + commit·2^b)/b: blowup 8 is
~33% worse than blowup 4 on commit time and RAM if commit/FFT
dominates the verifier prove, and only wins if witness generation
(hashing) dominates. Prediction: 3/34 is slower and fatter than 2/50.
Context: SP1 uses logBlowup 2 for its throughput recursion (compress)
and 3 only for terminal shrink/wrap; zisk's rate-1/8 layer sits at its
terminal SNARK boundary. Rate 1/8 is a "last proof" posture — keep it
in mind for the future terminal KZG/SP1 wrapper, not the fold tree.

## Bench to run

Harness: `bench-typecheck` (`lake build bench-typecheck`), the same
one behind the PR #605 comment. `--queries N` overrides the query
count of the active parameter set (inner and outer alike); blowup has
no flag — edit `Benchmarks/Typecheck.lean`
`recursiveCommitmentParameters.logBlowup` for point B.

Three points, equal conjectured ~100 bits, same host, same constants:

| point | logBlowup | queries | PoW | edit needed |
|---|---|---|---|---|
| A (baseline) | 2 | 50 | 0 | none |
| B (rate 1/8) | 2→**3** | 34 | 0 | one line, `recursiveCommitmentParameters` |
| C (PoW substitution) | 2 | 40 | **20** | one line, `recursiveFriParameters.queryProofOfWorkBits` |

Invocation per point (constants chosen to stay under a ~50 GB local
guard; on a ≥256 GB box add the heavy bench constants back):

```
bench-typecheck --ixe init-std.ixe --recursive --texray \
  --json point-A.json --queries 50 \
  --consts Nat.add_comm,String.append,Std.HashMap
```

Run points serially, never in parallel (RSS sampler + RAM guard).
Point A is worth rerunning locally rather than trusting the CI
comment, so all three points share a host.

## What to read off

- `fri-verifier-prove-time`, `fri-verifier-peak-rss`,
  `fri-verifier-proof-size` — the tree-layer cost. Uniform params per
  run means each point measures the steady-state tree (verifying a
  child produced under the same config), which is the right
  comparison.
- `ixvm-prove-time` / `ixvm-peak-ram` at point B — the top-level
  (Stage 1) penalty of blowup 8 on base proving. Prediction: ~2× LDE
  RAM/commit time; this is why blowup 3 must NOT be applied to the
  IxVM parameter set (it shrinks the per-shard RAM budget → more
  shards → more Stage 2 slots).
- texray `stark/…` vs `aiur/witness` spans — the witness-vs-commit
  split that decides H2 directly.

Decision rule: if B loses to A on either verifier prove-time or
peak-rss, settle the tree layer at logBlowup 2 and take the win from
queries (and from C's near-free PoW substitution: each PoW bit
replaces half a query at rate 1/4). If B wins, re-derive the Stage 2
RAM gate weights before adopting — the aggregate scheduler's 195 GiB
placeholders assume the current shape.

## Caveats

- Do not change `defaultFriParameters`/`defaultRecursionParameters` as
  part of this bench; production adoption additionally needs the
  security-policy decision (regime + bit target) and the aggregate
  cache/vk version bump that any parameter change implies.
- Bench rows are single-constant scale; ratios transfer to shard
  scale, absolute seconds don't. The production-scale calibration is
  one texray'd wrap + one structural join at the winning config.
- PoW=0 in A/B vs 20 in production: grinding adds prover wall time
  only at proof-generation start (negligible ≤2^25), but keep it in
  mind when comparing against production wrap timings.

# Part 2: single-box plan — r8i.metal-48xl (192 vCPU, 1536 GiB)

Goal: full Mathlib Stage 1 + Stage 2 on ONE machine, no distribution
tooling, at current security parameters. Baseline being improved: the
2026-09-02/03 production run — Stage 1 12.7 box-hours (239 shards,
serial per box), Stage 2 477 slots in 14:46 at `--jobs 2` on a
64-vCPU/495 GiB box.

Two structural facts drive everything (established in this thread):
Stage 2 work is `(2N−1) × ~constant slot cost` with N set by the
Stage-1 prover RAM ceiling, so RAM ceiling deletes recursion work; and
a single prove already saturates a 64-vCPU box's memory bandwidth
(measured: `--jobs 2` wall ≈ serialized wall), so throughput scales
with bandwidth-per-dollar, not cores or on-box concurrency.

## Configuration

- Shard at `--max-ram ~1300` (not 1400: reserve ~45 GB for the
  lookahead record + env + OS margin under the cgroup cap) →
  **N ≈ 80–85 shards**.
- Stage 1: one prove stream using the whole box; a lookahead thread
  executes shard k+1 during shard k's STARK phases (execution is
  serial, latency-bound, bandwidth-idle — it hides under the FFTs).
  Walk shards in size order so `E(k+1) ≈ 0.4·P(k+1) ≲ P(k)` and the
  pipeline never stalls. Lookahead is gated per pair on the manifest's
  measured peaks: start execute(k+1) only if
  `peak(k) + record_estimate(k+1) + margin` fits the box.
- Stage 2: `--direct-joins` (390 GiB direct-join envelope fits ~3×
  over in 1.5 TiB) → **~79–84 slots** instead of 477; `--jobs 3`,
  `--max-ram ~1400`.
- Every phase under a cgroup scope
  (`systemd-run --scope -p MemoryHigh=… -p MemoryMax=…`) so an OOM is
  a clean, restartable kill; retries resume via `--skip-proven` /
  aggregate cache.
- Pre-flight, once per partition: `ix prove --exec-only` over the
  candidate manifest (~40 min in parallel lanes, no STARKs) —
  validates the peak model at ~1300 GiB shard scale, surfaces every
  split before proving, finalizes the manifest. Add
  `IX_AIUR_QUERY_STATS=1` on a few shards to size query records
  exactly (record ≈ 5–10% of prove peak; whole-Mathlib record set
  ≈ 6–10 TB raw if ever persisted — lookahead keeps only one in RAM).

## Wall-clock estimate (current parameters: q=100, logBlowup 2)

Metal-48xl ≈ 3× a 16xlarge in memory bandwidth. Work in
16xl-box-hours:

| Phase | Work | Wall |
|---|---:|---:|
| Exec-only pre-flight (per partition) | ~3.5–4 (parallel lanes) | ~0.7 h |
| Stage 1 (~82 proofs, execute hidden) | ~9.2 | ~3.1 h |
| Stage 2 (~80 direct-join slots) | ~3.5 | ~1.2–1.6 h |
| Root validation + verify | — | minutes |
| **Total** | | **~4.5–5.5 h** |

vs ~28 h baseline: ~6× wall, and ~2× fewer instance-hours (28 → ~14)
because 477→~80 slots is deleted work, not parallelism. If Part 1
lands a q≈50-class recursion config, Stage 2 halves again → total
≈ 3.5–4 h. A second metal-48xl (fleet design from the session, at
metal granularity) roughly halves the totals once more.

## Uncertainties → experiments (run these first)

1. **Single-prove scaling across the box** (largest error bar): the
   estimate assumes one shard prove consumes ~3 bandwidth-units. Run
   the ~30-min pinning experiment — one mid-size shard proved at
   64-threads-pinned vs full-box-unpinned vs pinned NUMA lanes; check
   `lscpu` / `numactl --hardware` first (metal exposes true topology;
   if it's one socket, remote-DRAM concerns vanish). If effective
   scaling is only ~2 units, fall back to N≈160 @ ~700 GiB with two
   pinned lanes (Stage 2 grows to ~155 slots; total ~6.5 h).
2. **Peak-model extrapolation to ~1300 GiB shards**: exactly what the
   exec-only pre-flight checks; a miss costs a re-shard + another
   pass, never a failed prove.
3. THP enabled on the image (the `MADV_HUGEPAGE` record arenas depend
   on it); `perf` uncore counters available on metal for
   bandwidth/TLB diagnosis if numbers disagree with the model.

## Engineering bill

Exists already: `--direct-joins`, `--exec-only`, measured-peak
manifests, `--skip-proven` + aggregate-cache resume,
`IX_AIUR_QUERY_STATS`. To build: the **lookahead execute thread** in
the Rust shard-prove driver with the per-pair RAM gate
(`shardProveWithEnv` is currently monolithic execute+witness+prove —
this is the one real piece of new code; worth ~25–30% of Stage 1
wall), plus operational scripting (NUMA pinning, cgroup scopes, retry
loop). Deferred, not needed for this plan: query-record serialization
(raw header+arena dump if ever built — no serde framework, no
database) and all multi-node distribution tooling (`--root-slot`,
store sync, split healing) until a second box joins.

Caveat to record in provenance: an N≈80 partition makes every future
re-prove of a shard require a ≳1.3 TiB box.
