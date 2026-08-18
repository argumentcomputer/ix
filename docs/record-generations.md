# Record generations: principled rollback for segment boundaries

Status: **SUPERSEDED — kept as the analysis record.** A follow-up audit
found this design not implementable as specified: under free-running
workers there is NO block-consistent capture instant (entry insertion is
two-phase — keys/PENDING publish before outputs complete below the
watermark), the copy-on-first-write journal has a first-touch TAS race,
the seal set is ill-defined under out-of-order completion, and
post-seal-claim overshoot is uncovered. The successor design —
**B3, quiescent-suffix transactions** (drain at geometric headroom
points; snapshot lengths + full multiplicity arrays at quiescence; no
journal, no bump-path tax) — dissolves all four findings and is specified
with its adopted amendments in `docs/segment-sizing-design-space.md`
(§1 B3 + "B3 amendments"). §§3, 5.1–5.2, 7 below (rollback consistency
arguments, zero proving cost, the eviction disqualification) survive
unchanged and are inherited by B3; §2's capture mechanism and §4's
free-running cadence do not. One wording correction inherited by B3:
restored state is *witness-equivalent*, not "bit-equivalent" — physical
RSS (stripe capacity, arena pages, SharedIO) does not roll back and must
be accounted separately.

Originally: proposed successor to the grab-time admission controller
(`docs/segment-admission.md`, implemented at `703940c`). Written after a
soundness audit of a competing design ("eviction by unexecution") found a
disqualifying architectural limitation; that audit's findings are
summarized in §7 because they motivate this design and constrain any
alternative a reviewer might prefer.

## 0. One-paragraph summary

The shared `QueryRecord` is append-only in everything except multiplicity
words. A *generation* is therefore cheap to capture: per-map length
watermarks, a snapshot of the two fixed-size byte-gadget counter tables, the
exact model peak at that instant, plus a copy-on-first-write journal of
multiplicity changes since the previous generation. Rollback truncates
lengths to a watermark, removes truncated indices from the stripe hash
tables (by their already-stored hashes), replays the journal, and restores
the counter cells — restoring the record **bit-equivalent** to its state at
that generation. Segment boundaries then stop being predictions: run until
the metric crosses the acceptance line, pick the newest generation whose
*recorded, measured* peak fits, roll back to it, seal. Every estimator,
projection, trim, and replay in the current controller becomes unnecessary.
The prover never sees any of it.

## 1. Problem recap (why boundary control keeps growing machinery)

A segment is provable iff its padded peak-prove-RSS model value fits the
acceptance line. Two facts force all existing complexity:

1. A block's cost is unknowable before executing it (defeq/delta-unfolding
   dominated; serialized size is only a regional proxy).
2. The record is irreversible: multiplicities are shared interleaved atomic
   counters with no per-block attribution, so an overshooting record cannot
   shed blocks. Today's only rollback is re-executing a shorter prefix into
   a fresh record ("trim-replay").

The implemented admission controller (`docs/segment-admission.md`) reduced
trims from ~1.0/segment to ~0.2/segment on the worst env and to zero on
init/initstd, at the cost of: a marginal density estimator, a
watcher-published ratio with staleness, residual trims where the estimator's
window mispredicts, and chronic underfill on high-variance envs (FLT seals
average ~60% of the line → more segments → more re-derived boundary tail →
more total proving). Review of that design (three independent agents)
converged on: the architecture is fine, the estimator is the weak part, and
exact zero-trims-with-good-fill is impossible **while the record cannot roll
back**. This design removes that premise.

## 2. What a generation is

State of the record, partitioned by mutation discipline:

| component | mutation pattern | generation capture |
|---|---|---|
| entry arenas (keys/outputs), per map | append-only | length watermark (one `usize` per map) |
| stripe hash tables (`u32` indices) | insert-only | nothing (rollback removes truncated indices; per-entry hashes are already stored for table growth — no rehashing) |
| multiplicity words | in-place atomic RMW | **copy-on-first-write journal** + per-epoch dirty bitmap |
| byte-gadget tables (`Bytes1Queries` 256 rows, `Bytes2Queries` 65,536 rows) | in-place counter bumps | full snapshot (~0.5 MB, trivial) |
| io arenas (`IOBuffer`/`SharedIO`) | append-only, advice | **left alone** (see §5.3) |
| model peak | derived | one `peak_prove_bytes` eval stored as generation metadata |

The journal mechanism: each multiplicity word's *first* modification within
the current epoch appends `(map, index, old_value)` to an epoch journal;
"first" is detected by a test-and-set in a per-epoch dirty bitmap (1 bit per
entry, indexed by entry index per map). Subsequent bumps in the same epoch
pay one bitmap load. Journals are sharded per thread to avoid contention.

Generation cadence: one per completed cohort (one block per worker,
~63 blocks) — the unit derived from the concurrency structure, not
wall-clock. Capture cost per generation: watermark reads (trivial), byte
snapshot (~0.5 MB), bitmap clear (memset, 1 bit/entry ≈ 60 MB per 500M
entries ≈ ~10 ms), one model eval (µs).

## 3. Rollback

To restore generation G (workers stopped, single-threaded — this only ever
happens at a segment boundary):

1. For each map: for indices in `[watermark_G, len)`, remove the index from
   its stripe table using the stored hash; then truncate `len` to the
   watermark. (Arena segments are not freed; the next segment's insertions
   physically reuse the slots.)
2. Replay all journals of epochs newer than G in reverse: restore each
   journaled `(map, index, old_value)`.
3. Restore the byte-gadget counter snapshots.
4. Done. The record is bit-equivalent to its state when G was captured.

Consistency arguments (each one structural, none statistical):

- **No dangling references**: a surviving entry cannot reference a truncated
  one — the survivor existed before the truncated entry was ever inserted,
  and entries never mutate after completion. This includes memory pointers:
  truncation rewinds a *suffix of insertion time*, so pointer contiguity of
  the surviving prefix is untouched. (This is precisely what per-block
  eviction could not provide — see §7.)
- **Probe caches self-invalidate**: the per-thread probe cache already
  revalidates every hit by `index < len` + full key compare; truncated
  indices fail the length check.
- **No pending state**: rollback runs with workers drained; the
  reservation/pending machinery is quiescent (and would be poisoned by the
  existing chokepoints otherwise).
- **Model correctness for free**: unlike eviction, no live-vs-dead
  accounting is needed anywhere — truncated lengths ARE the true lengths;
  `peak_prove_bytes` and trace generation read real state unchanged.

## 4. The boundary algorithm this enables

```
loop:
  workers grab blocks freely
  (single cheap grab check: metric >= acceptance_line -> stop grabbing)
  every completed cohort: capture generation (watermarks, counters, peak)

at stop (drain complete):
  G* := newest generation with recorded_peak <= acceptance_line
  roll back to G*
  seal, run verify_segment over G*'s blocks, prove
  next segment starts at G*'s schedule position
  (rolled-back blocks re-execute there, into reused arena slots)
```

Properties:

- **The boundary is selected among measured states, not predicted ones.**
  Every candidate's peak was computed on the actual record at that instant.
  There is no estimator, no ratio, no window, no projection, no trim, no
  geometric descent, and no replay of kept work — all of
  `docs/segment-admission.md` §2.1's machinery and §2.2's items 2–3 are
  deleted rather than repaired.
- **Fill**: within one cohort of the line, on any env, first run — versus
  admission's ~60% on FLT-class variance. Fewer segments → less boundary
  tail re-derivation → less total proving (the dominant cost).
- **Waste per boundary**: the execution of blocks past G* (≈ overshoot
  cohorts, typically 1–2), analogous to today's drain, plus rollback itself
  (O(touched set of rolled-back epochs) — seconds). No kept-prefix
  re-execution ever (trim-replay's cost).
- **Monsters**: a single block whose completion jumps the metric from
  under-line to over-budget rolls back to the generation before it and gets
  isolated in its own next segment — the same UNPROVEN inventory path as
  today if it exceeds budget alone. Unchanged.

## 5. Costs

### 5.1 Proving cost: none, with a dividend

Nothing enters the proof system: no columns, no lookups, no constraint or
claim changes. By seal time the rollback has happened; the sealed record is
bit-equivalent to one produced by a clairvoyant single-pass execution of
exactly the kept blocks. The prover cannot distinguish it. Second-order
effect is a proving *benefit* via fill (fewer, fuller segments).

### 5.2 No hashing

Generations here are positional, not content-addressed (the Nix analogy is
about the generation/rollback discipline, not about hashing): identity is
(map, index, length). The only hash-adjacent operation — removing truncated
indices from stripe tables — uses the per-entry hashes the map already
stores for table growth. Zero cryptographic or non-cryptographic hashing is
added anywhere.

### 5.3 Execution cost (the entire cost story)

- **Bump-path tax** — the one number that decides the design: the dirty
  bitmap adds a test-and-set on an entry's first bump per epoch and one load
  on subsequent bumps, on the hottest path in the system. To be measured
  first (see §8). If ≤ ~2% on the init exec benchmark: run always-on, zero
  knobs. If more: gate epoching to a boundary tail (activate when the metric
  enters the final stretch), keeping the bulk path untouched at the price of
  one activation threshold.
- Per-generation capture: ~10 ms bitmap clear + trivial snapshots, ~1/s.
- Journal RAM: `8–16 B × entries touched per epoch` (cohort-local working
  sets: tens of MB), plus 1 bit/entry bitmap (~60 MB per 500M entries).
- io arenas are deliberately not rolled back: io is insert-if-absent advice,
  already shared across segments; entries faulted by rolled-back blocks are
  harmless over-provision, and their next-segment re-execution hits them.

## 6. Soundness summary

There is no inverse-accounting argument to audit — that is the design's main
virtue over unexecution. Rollback restores bit-equivalent state; the sealed
record *is* a record of executing the kept blocks. Warm-mode/`verify_segment`
interplay is unchanged (the seal claim is built after rollback over exactly
G*'s blocks). Failure of the machinery (bitmap/journal bug) corrupts counts
and produces an unbalanced witness → proof generation or verification fails —
the same fail-closed property as warm mode. It cannot produce a wrong proof.

## 7. Why not per-block eviction ("unexecution") — audit result

A competing design — remove an over-budget block by replaying its body with
decrements, cascading at zero — was audited first. Findings:

- The inverse-accounting core is sound: call-site consumption is once per
  call per row (`trace.rs` `Op::Call` pushes with multiplicity ONE), provides
  are mult-scaled, mult-0 function rows are filtered; deterministic replay
  reproduces the exact bump multiset; a no-false-cascade invariant holds
  (a survivor's running count never transiently hits zero). One subtlety
  found: replayed return-inserts must be mult-no-ops or they double-remove.
- **Disqualifying limitation**: memory-circuit rows are positional (the
  pointer IS the entry index) with a consecutive-pointer constraint, so
  dead memory entries keep their rows forever — eviction cannot reclaim
  memory-table trace heights, and memory tables (expression-store traffic)
  plausibly dominate exactly the dense-region overshoots that matter.
  Fixing that means renumbering pointers (cascades into every key embedding
  a pointer — a full rebuild) or a gap-tolerant memory circuit (invasive,
  adds range checks — real proving cost).

Generations sidestep this completely: rewinding a suffix of insertion time
preserves pointer contiguity by construction, so memory heights genuinely
shrink.

## 8. Implementation and validation plan

1. **Prototype the write path only** (bitmap + journal + capture; no
   rollback): measure the bump-path tax on the init exec benchmark
   (3:00 baseline at 63 threads). This is the go/no-go gate. (~1 day)
2. Rollback + boundary selection in `scan.rs`; delete admission, trace-trim,
   geometric descent (keep the UNPROVEN path and the watcher as a plain
   metric sampler). Net LOC in `scan.rs` expected negative. (~1–2 days)
3. Validation ladder: init dry (expect ≥ 7 segments, 0 trims, seals within
   one cohort of the line), FLT 130k prefix dry (expect ~35–40 segments vs
   admission's 58, zero trims, wall ≤ 35:42), real init + initstd proves
   (expect ≤ 23:45 / ≤ 40:07 with fewer segments), full FLT dry.
4. The failure conditions that would send us back: bump tax > ~5% always-on
   AND tail-gating measurably distorts the boundary region; or journal RAM
   surprises on pathological envs.

## 9. Review questions

- Is the per-epoch dirty bitmap the right first-touch detector, or is an
  epoch tag word per entry (8 B/entry, no per-epoch clear) better despite
  the RAM? The clear is O(entries) per epoch; the tag is O(0) per epoch but
  doubles mult storage and adds a compare on every bump.
- Cohort-cadence generations give one candidate boundary per ~63 blocks. Is
  finer granularity near the line worth capturing (e.g., per-completion in
  the last stretch), or does the UNPROVEN path adequately cover the
  monster-jump case?
- Stripe-table removal is O(truncated entries) with a lock per stripe;
  rollback is single-threaded. Any reason to parallelize (per-stripe) from
  day one, or measure first?
- The bulk/tail gating fallback introduces one activation threshold if the
  always-on tax is too high. Is there a structural activation point (e.g.,
  first generation whose peak exceeds line − k cohort-deltas, with k from
  measured cohort deltas) that avoids a constant?
- io non-rollback (§5.3): confirm no io consumption accounting exists on
  any prover path (audited: `IOBuffer::get_info` is pure lookup+fault-in;
  no counters found). A second pair of eyes on `SharedIO` specifically.
