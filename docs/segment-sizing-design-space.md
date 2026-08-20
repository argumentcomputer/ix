# Segment sizing: the complete design space, and the work queue

Written 2026-08-14 at session pause. Consolidates four agents' designs and
reviews plus all measurements. Companion docs: `segment-admission.md` (the
implemented baseline), `record-generations.md` (audited, amendments listed
below). The stated mission: **accurately sized segments — zero trims, good
fill — on any env, without heavy overhead.** The honest headline: nothing
proposed so far *predicts* segment size accurately, because block cost is
unknowable pre-execution; the viable end-states either measure-and-rollback
(exact, pays checkpoint machinery) or estimate-and-recover (cheap, pays
occasional trims and underfill). Everything below is organized around that
fork.

## 1. The design space (everything considered, with verdicts)

### A. Online estimators (single pass, advisory, exact recovery underneath)

| # | idea | status | verdict |
|---|---|---|---|
| A1 | metric polling + trim-replay | shipped pre-admission | routine trims in dense regions; superseded |
| A2 | grab-time metric check | shipped briefly | halves detection latency; insufficient alone |
| A3 | **grab-time admission, marginal density ratio** | **SHIPPED `703940c` — the baseline** | measured best: 0 trims init/initstd end-to-end, ~0.16/seg on FLT; underfills FLT to ~60% of line |
| A4 | cumulative ratio | built, measured | worker-count overpricing → sliver segments; rejected |
| A5 | 5-window median ratio | built, measured | lags density ramps → late stops, trims; rejected |
| A6 | padding-staircase reserve (`peak + max_step`) | built, measured | sound but blunt: underfill AND residual multi-step trims; rejected (`max_step` kept as diagnostic) |
| A7 | raw-vector projection: per-circuit Δraw-rows growth per completed static byte, projected reservations passed through the exact padded model (`peak_prove_bytes_from_raws`) | designed (agent 2), unbuilt | fixes A3's real defect — the scalar ratio differentiates a *staircase* (near-zero between padding cliffs → overshoot; spikes at cliffs → underfill). Best remaining estimator idea; still an estimator |

### B. Exact controllers (measure real states, roll back to one)

| # | idea | status | verdict |
|---|---|---|---|
| B1 | eviction by unexecution (deterministic decrement replay + cascade) | audited | inverse accounting sound (with the insert-no-op subtlety); **disqualified**: memory rows are positional (pointer = index, consecutive-pointer AIR constraint) so memory heights never shrink — recovery power absent exactly where overshoots live |
| B2 | generations, COW mult journal, free-running capture | audited (`record-generations.md`) | **not implementable as specified**: no block-consistent capture instant exists under free-running workers (two-phase append: keys/PENDING published before outputs complete below the watermark); journal first-touch race; seal-set ill-defined under out-of-order completion; post-seal-claim overshoot uncovered |
| B3 | **quiescent-suffix transactions, geometric checkpoints** (agent 3; = B2 + audit amendments + one simplification) | designed, unbuilt — **the exact-controller candidate** | drain workers at geometric headroom points (half the remaining RAM/FFT headroom → log-many drains/segment); snapshot per-map lengths + **full multiplicity arrays (~2 GiB per 250M-query record)** + byte counters; speculative epoch at full 63-way width; exact post-`verify_segment` acceptance; commit, or restore+truncate+retry a smaller prefix. Full-snapshot-at-quiescence dissolves B2's blocker AND journal races AND the bump-path tax. Open costs: drain straggler tail (a monster in flight stalls each drain — measure), truncation machinery (stripe-table suffix removal — mechanics verified sound by audit; probe-cache generation salt; arena/tail reclaim), retry granularity |
| B4 | per-block transactional overlays | sketched (agent 2, earlier) | superseded by B3 — suffix granularity suffices and avoids per-block provenance |

### C. Planning / caching (multi-pass or cross-run)

| # | idea | status | verdict |
|---|---|---|---|
| C1 | manifest-first exact planner (plan pass → cached manifest → fixed-range execution) | analyzed | segment geometry depends on the boundaries themselves (fresh-record tail re-derivation), so exact planning either *is* online cutting or needs provenance; rejected as a primary mechanism |
| C2 | **boundary caching** (record accepted boundaries from any successful run; reuse on re-proves; invalidate on env/toolchain/params change) | trivial, unbuilt | works as an adjunct to ANY controller; makes repeat runs zero-trim by definition; cache hit-rate ≈ 0 for evolving envs, high for release artifacts |

### D. Deep-architecture (change what a block or record is)

| # | idea | verdict |
|---|---|---|
| D1 | query provenance / per-block attribution ledger | rejected repeatedly: taxes the hottest path to serve a rare event |
| D2 | sparse/gap-tolerant memory AIR, or pointer renumbering | invasive, adds range checks / cascading rebuilds — real proving cost; only relevant if B1-style eviction is ever revived |
| D3 | cross-proof row aggregation (Phase C) — **prover-side row sharding** | FEASIBILITY ANALYZED 2026-08-14 (two agents, multi-stark rev `c72d321` + aiur AIR/witness): **nothing blocks it at either layer.** Execute the whole env once; the prover partitions each circuit's rows into RAM-sized chunks; one shared (β,γ) drawn after ALL chunks' stage-1 commitments (the prover pipeline has a clean seam exactly there, `prover.rs:351→377`); per-proof zero-balance check (`verifier.rs:242-246`, already a public transcript-bound accumulator) relaxes to Σ across shards = 0 in the recursive aggregator. Function circuits are subset-closed (zero transition constraints — memory.rs is the only `main_next` user in the crate); memory needs a one-line base-pointer offset (`row[2] = base + i`) plus boundary continuity via first/last-row-gated lookups telescoping through the shared channel (zero library changes); byte gadgets: per-shard recount or one designated shard; the single whole-env claim can sit in any shard. Dissolves the atomic-block limit (monsters become rows), makes trims impossible by construction, and reduces the executor's cut criterion to a trivially measured heap threshold. Costs: two-phase transcripting in multi-stark + its in-circuit Lean mirror (the dominant item), ~2× trace-gen wall (regenerate chunk traces in phase 2 from the persistent record — no re-execution), whole-record residency (mmap/spill; revives u64 map indices for Mathlib-scale), aggregator entrypoint. |
| D4 | preemptible block execution (safe pause points inside a block) | unexplored; overlaps D3's benefit; likely deep interpreter/codegen surgery |

### B3 amendments (fourth review, 2026-08-14 — adopted)

A fourth independent review endorsed B3 as the leading candidate and
corrected several overstated guarantees; all adopted:

1. **The QueryMap len-runaway (§3) is a hard prerequisite, not parallel
   work.** B3 treats map lengths as authoritative transaction watermarks
   and reuses truncated indices; building on a counter that can run away
   is building on sand. No B3 implementation until §3.1 is root-caused
   and stress-tested.
2. **Honest guarantee wording**: *zero re-execution of the committed
   prefix; bounded speculative suffix re-execution.* Rolled-back blocks
   run twice (speculatively in segment N, really in N+1). Geometric
   spacing bounds discarded metric growth, **not** discarded wall time
   (a slow block can add little metric). Benchmarks must report
   rollback events, speculative block executions, speculative
   wall/core-seconds, and committed-prefix replays as separate counters.
3. **Trial-claim protocol**: a checkpoint is only certified after
   `verify_segment` runs, and the trial claim itself must be rolled back
   before resuming — so the commit path transiently holds TWO mult
   snapshots (~4 GiB at FLT scale), and discarded trial claims seed
   shared ch-0 io data that must be rolled back or explicitly counted as
   residency. **MVP seals the last certified checkpoint — no
   prefix-refinement retry loop** (refinement can re-execute a monster
   repeatedly; add only if measured fill demands it).
4. **Logical rollback ≠ physical-RAM rollback**: truncation leaves
   stripe-table capacity, resident arena pages, and monotonic SharedIO
   behind, and `record_retained_bytes` stops seeing those pages. Phase-1
   measurements must verify post-rollback **RSS**, not just restored
   lengths/model values. Call the property "witness-equivalent", not
   "bit-equivalent".
5. **Probe-cache invalidation is mandatory**: the per-thread probe cache
   assumes completion is permanent; after index reuse a stale
   (key, index) can match a new pending entry. Fix via a record
   generation salt read into a **thread-local** once per epoch resume
   (not an atomic load per probe).
6. **Padded FFT metric first**: `fft_cost_from_raws` uses raw heights;
   exact FFT-side sizing claims require the padded, phase-aware work
   metric implemented and validated before B3 can claim exactness on
   that axis.
7. **Geometric checkpoints carry residual policy** (halvings-before-seal,
   padding cliffs skipping targets, combining RAM/FFT headroom,
   termination) and may cost 8–12 drains, not the assumed ~6 — measure
   the actual count in Phase 1.

Revised sequence: (1) A3 CAS + watcher-ordering fixes → (2) §3
root-cause + fail-soft + stress tests → (3) padded FFT metric →
(4) drain-cost measurement (idle core-seconds, tail latency, trial-claim
cost, checkpoint count) → (5) snapshot/restore/truncate microbenches
(incl. two simultaneous snapshots, table shrink, arena reclaim, same-key
retry) → (6) last-certified-checkpoint B3 MVP behind its own flag, run
WITHOUT admission (admission would mask B3's behavior) → (7) prefix
refinement only if fill demands → (8) boundary caching (C2) as hints
with an exact seal check, once geometry proves deterministic.

### Gate-1 measurements (2026-08-14, `IX_SCAN_DRAIN_PROBE=1`) — and what
### they say about the fork

Drain-cost numbers from real geometric-headroom drains (pause grabs,
wait out in-flight blocks, quiescent certified sample, resume):

- **Smooth regions** (init; FLT outside the dense core): 0.1–10 s per
  drain, typically ≤5 s; ~13 probes over init's 7 segments.
- **FLT dense core** (window 100k–115k): **97–100 s per drain, ~6,000
  idle core-seconds each** — a monster block in flight stalls all 63
  workers for its full remaining runtime.

Reading: drains are cheap exactly where B3 helps (smooth growth, where
admission underfills) and brutal exactly where B3 cannot help anyway — a
head-of-span monster forces its own re-execution under ANY rollback
controller (B3 would roll back to the checkpoint before it and re-run it
alone, the same waste as admission's trim, PLUS the drain tax). Combined
with the same day's admission upgrades (grab-granular certified samples;
the head-pinned trim rule that isolates a measured head monster in one
round), the trim path now converges in one round with near-optimal keep,
so B3's remaining edge over fixed-up admission is only the kept-prefix
replay cost on ~0.2 trims/segment (FLT) — against log-many drains per
segment everywhere. **Verdict so far: full geometric B3 does NOT beat
the repaired admission baseline on FLT-class content; a B3-lite
(quiescent certification only in smooth regions near the line) is the
only variant still worth costing.** Gate 2 (snapshot/restore/truncate
microbenches) remains unmeasured and only matters if B3-lite advances.

Confirmation ladder on FLT 130k (same env, same box, one variable per
row; all runs 129,998/130,000 blocks — the 2 rejects are the §4
divergences):

| build | segments | trims | multi-round replays | wall |
|---|---|---|---|---|
| baseline `703940c` | 58 | 13 | 1 | 35:42 |
| + §2 fixes 1–3 | 56 | 15 | 1 | 36:24 |
| + grab-granular samples | 56 | 12 | 1 | 35:32 |
| + head-pinned trim (`11e1225`) | 61 | 12 | **0** | **34:37** |

Honest nuance on the head-pinned rule: "under-line samples exist only at
`f == seg_start`" certifies that keep=1 is the only prefix WITH a
certificate — it does not prove the head block alone crossed the line
(concurrent work racing it contributes too). The cost of that
conservatism is sliver segments (61 vs 56; one sealed a lone block at
104 GiB); the measured net is still the best wall of the ladder, but a
future refinement could re-trim upward once the isolated head reseals
far under the line.

### The fork, stated plainly

- If the mission is *zero trims with good fill on any env*: **B3** is the only
  designed candidate that achieves it without estimators — at the price of
  log-many drain barriers per segment whose straggler cost is unmeasured.
  Its go/no-go gates: (i) drain-stall cost on init + an FLT dense window,
  (ii) snapshot/truncate wall time. Both measurable with a thin prototype.
- If occasional exact-recovery trims (~0.16/seg worst measured) and FLT
  underfill are acceptable: **A3 + its bug fixes (§2)**, optionally upgraded
  by **A7**, is already shipped and measured, with C2 layered for repeat runs.
- The two compose: B3 could replace A3 behind a flag and be judged on the
  same dry-run ladder (init, FLT 130k prefix, full FLT) against A3's numbers:
  init 23:45 / initstd 40:07 end-to-end, FLT prefix 13 trims / 35:42.

## 2. Work queue: the implemented baseline (A3) — correctness fixes

Found by two independent reviews; all confirmed against code. **Items 1–3
FIXED in the working tree 2026-08-14 (validation dry runs pending):**

1. ~~**Watcher sample ordering**~~ FIXED: the watcher now reads the
   frontier BEFORE the model eval, so every sample's prefix closure is a
   subset of what the eval measured (concurrent completions only inflate
   the metric — conservative).
2. ~~**Admission reservation race**~~ FIXED: admission and reservation
   are one atomic step — a worker prices the block at the current cursor
   and CASes the cursor past it; a lost CAS reprices at the new cursor.
   Refusal (worker admission or watcher backstop) sets a `CLOSED_BIT`
   packed into the cursor word, making refusal terminal for the span.
   Replay spans keep plain `fetch_add` (no admission there).
3. ~~**Trim line excludes the seal-claim cost**~~ FIXED: the seal
   measures the claim's model delta (peak before/after running
   `verify_segment`) and the trim now requires
   `sample + claim_delta <= line`, closing the epsilon-over reseal
   (geometric-descent pinning) case.
4. Optional precision: publish certified `(frontier, metric)` samples from
   the grab checks (workers already compute the metric), making residual
   trims close and single-round without the 500 ms granularity.
5. Optional upgrade: A7 (raw-vector projection) replacing the scalar ratio.

## 3. Work queue: the crashing / unexecutable constant (NEW failure class)

Discovered by the full-FLT dry run (2026-08-13): during segment 121 (start
298,103; crash after `done` = 303,104) one `QueryMap`'s LENGTH hit the
**2^32-entry architectural cap** (`querymap.rs:658` assert → SIGABRT, whole
run dead at 70% of FLT). Telemetry: 843M voluntary context switches, 26
CPU-hours of system time in ~43 wall minutes.

**DIAGNOSIS REVISED TWICE — final picture (2026-08-14 audit +
forensics).** Not a monster block (the span re-ran clean in 143 s,
`monster-hunt2.log`), and not a spinning counter either: the "25 GB RSS"
premise was a telemetry artifact — the `[exec]` RSS print only fires on
block completions, which froze when the runaway started. `/usr/bin/time`
recorded **Maximum RSS 404 GiB**, fully consistent with ~2^32 REAL
entries. A dedicated audit traced every len-advancing path: all three
run under the per-map alloc mutex after a table-find miss and write
≥16 B/entry first — len physically cannot advance without allocation.
So the runaway was a **garbage-key cascade**: some thread consumed a
junk field element (an unwritten output) and FLT's numeric-recursive
functions minted one new distinct key per recursion level for ~40
minutes, while the poison-reclaim storm (M3 below) produced the 843M
context switches. Nondeterministic ✓, env-independent ✓.

Audit findings (all verified against code) and their status:

1. ~~**M1**: `insert_cc`'s existing-entry bump lacked a pending check —
   `POISONED+1` matches neither the reclaim test nor the waiter break:
   an absorbing state parking every future prober forever~~ **FIXED**
   (bump gated on `m & MULT_PENDING == 0`; reclaim + waiter tests made
   masked instead of exact-match).
2. ~~**M2**: completion has no ownership check and the reservation pop
   only matched the list tail — a reservation completed by another
   thread stayed on the owner's list forever; a later error then
   poisoned a live completed entry (or, across a record replacement,
   scribbled freed memory)~~ **FIXED** (search-remove in both resolve
   branches; poison is now a CAS restricted to live pending words with
   a loud report otherwise; hard assert at the chokepoint that a
   successful execution leaves zero reservations).
3. ~~**M3**: outermost-first poison drain made every waiter chase the
   poisoner down the chain — one wake-all storm per level per waiter
   (the futex-storm amplifier)~~ **FIXED** (innermost-first drain).
   Full damping (a terminal `MULT_FAILED` state so blocks over a known-
   failing cone fail fast instead of re-executing it per block) is a
   follow-up.
4. ~~**M4a**: `debump` subtracted before asserting — `PENDING−1` clears
   the tag bit and lets waiters read the unwritten output in the
   pre-abort window~~ **FIXED** (check before subtract). Log forensics:
   no debump assert fired in the dying run, so this was not the
   injector there.
5. ~~**M4b**: probe-cache tags mixed the map ADDRESS — addresses recur
   across record replacements (121 in the dying run), and a stale tag
   can validate against a NEW map's PENDING entry (key written at
   reserve, output not) → junk output read. The leading injector
   candidate~~ **FIXED** (never-reused per-map construction salt).
6. **Invariants added**: per-map `open` pending-entry counter asserted
   zero at every seal (names the map at the seal instead of dying at
   2^32); watcher stall detector (logs open reservations + longest map
   when `done` freezes ≥60 s — would have named the pathology in one
   minute instead of 40); full-map asserts now name strides + open
   count. NOTE: `panic = "abort"` workspace-wide, so catch_unwind
   fail-soft is impossible and the PoisonOnUnwind guard's unwind arm is
   dead code — containment is exactly these early-tripping invariants.
7. **Open**: 63-thread stress test with injected failures (natural
   poison sources: the §4 divergent constants) + loom/shuttle model
   check of the mult-word state machine; if a runaway recurs with the
   fixes in, audit the SharedIO fault-in path next (the remaining
   unaudited junk source).
8. (Downgraded) u64 entry indices / capacity policy: only relevant if a
   genuine ≥2^32-entry block is ever demonstrated; none has been.

## 4. Work queue: the three Aiur/Rust kernel divergences

All fail in-circuit with `no match case for value 0` on constants `check-rs`
certifies clean; all reproduce on the fresh (post-`fc4f43a`) env:

| block address (flt.ixe) | name |
|---|---|
| `624c4aa2…` | `Ix.«624c4aa2…»._private.Batteries.Data.MLList.Basic.0.MLList.MLListImpl.rec` |
| `8e6457040…` | `Ix.«8e6457040…»._private.Batteries.Data.MLList.Basic.0.MLList.MLListImpl` |
| `c079e20b…` | `OrderedFinpartition.extendEquiv._proof_11` |

The third (a plain Mathlib proof term) breaks the nested-inductive-only
theory: either one shared unhandled variant is reachable from several
construct families, or there are multiple gaps. Plan: repro each with
`ix check --ixe flt.ixe '<name>'` then `--interp source` for the rich error
naming the exact kernel `match`; fix the missing arm(s) in the IxVM kernel
Lean; regen codegen; add regression fixtures via `ix shard extract` bundles
(hash-stable minimal `.ixe`s). Names are toolchain-relative: the `Ix.«hash»`
prefix is the constant's own content address — colleagues on other commits
should locate by suffix. Until fixed, "FLT fully proven" is impossible:
these blocks' segments are excluded from proving.

## 5. Other open items (unchanged, for completeness)

- Rebase onto `origin/main` (now `5392d37`, recursive-verifier changes →
  codegen regen) and push (user's call; 40+ commits unpushed).
- PR 550 decision: merge as diagnostics with reworded scope + the
  `cutClosureShards` `--profile` fix (two-line, written but dropped during a
  branch dance — must be re-applied on that branch) + make `ix bench shard`
  propagate failures; conflicts with our branch in 4 files, one semantic.
- Suffix-match name resolution: user is taking this to a separate branch.
- `.ixe` compiler-version stamp at `EnvHandle` load.
- Docs uncommitted: `segment-admission.md`, `record-generations.md`
  (amendments from the audit NOT yet folded in), this file.
- FLT inventory (partial, 70%): 121 segments, 19 trims, 0 UNPROVEN, mean
  seal 289 GiB — logs preserved in the session scratchpad; will not survive
  a reboot (tmpfs) — copy out if wanted.
