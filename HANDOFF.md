# Handoff: OOC/Zisk kernel perf (branch `sb/inst-univ-memo`)

Working note for whoever continues this line — delete before merging.
Written 2026-07-31. Campaign context: after #442 (uid-identity, symbolic
Nat offsets, env-machine WHNF) landed on main, interning became the
dominant predicted-cost axis (47.8% of Zisk cost units on InitStd).
This branch is the first two levers against it.

## What this branch is

Two commits on post-#442 main:

1. `kernel: memoize universe instantiation, reuse unchanged subtrees` —
   cross-call `(expr addr, us id)` memo in the intern table + every
   rebuild arm returns the input node when children come back
   pointer-identical (under uid-identity, a rebuilt unchanged subtree is
   a *different* tree — fresh uids — so ptr-reuse is a RAM lever, not
   just cycles).
2. `kernel: defer anon Defn value conversion where deps are trusted` —
   type converts at fault-in, value on first demand; gated by
   `KEnv::defer_defn_values` (default OFF, whole-env anon runner opts in).

Measured (base = main content, interleaved where noted):

| metric | commit 1 | + commit 2 |
|---|---|---|
| OOC whole-env InitStd | −5.6% | −11.1% cumulative |
| OOC whole-env Init (interleaved A/B) | | −6.7% cumulative |
| OOC closure peak RAM | −11..−40% | ~unchanged |
| Zisk guest cycles (8 closures) | −6.8%, all rows | byte-neutral (+0.03%) |

## Where the remaining cost lives (Init, measured attribution)

Intern events after commit 1: subst 30.2% / ingress 25.5% (71.6% of it
value conversion — commit 2's target) / defeq-proper 13.0% /
infer-proper 12.5% / whnf-proper 8.4% / abstract 5.1% / inst_univ
residual 5.0%. Reproduce with branch `sb/ooc-intern-probe` (RAII
context guards around ingress/subst/inst_univ/abstract/lctx/whnf/
defeq/infer + a value-conversion split; never merge it, and NEVER take
wall-clock from a probe build — its two shared atomics per intern event
cache-line-ping-pong multi-worker runs up to ~6x).

## Remaining big wins, ranked

1. **Machine-native delta at the Rust whnf layer.** The subst context
   (30% of intern events; the standalone subst counter is another 30.6%
   of predicted cost) is dominated by readback between delta steps: the
   machine materializes at every `whnf_core` exit and the next unfold
   re-enters immediately. Known constraint from the #442 port:
   `whnf_core` must stay delta-free (def-eq lazy-delta unfold ordering),
   so this is a designed restructure of *whnf's* delta loop with
   closures. Working blueprint: the IxVM port's `mwhnf_const` Defn arm
   (branch `sb/aiur-machine-v2`, worktree `~/ix-machine` — family-0
   non-proj-def Defns unfold with the closure spine intact) plus the
   June IxVM C1.5 measurements (delta chains pay zero readback). Largest
   single remaining axis; expect the win concentrated on
   reduction-heavy blocks, i.e. shard-floor setters.

2. **Guest-scope value laziness, second attempt.** Universal deferral
   regressed the guest +1.7% because closure/shard scope demands nearly
   every value and the type/value conversion SPLIT loses their shared
   per-constant caches. Two upgrades would flip it: (a) make the split
   free — persist the per-constant conversion cache (sharing-table hits)
   so a demanded value converts as cheaply as it would have inline; then
   the flag can default on everywhere and shard FOREIGN constants
   (touched type-only — the majority per measured-ingress) stop paying
   value conversion in-guest; (b) shard-pipeline synergy: record
   VALUE-demanded separately in the touch graph (`TypeChecker::touched`
   machinery is right there) so the packer knows which foreign values a
   shard can ship without. (The Aiur-side type-only witness tier built
   on the same recording is out of scope here — protocol/claim work.)

3. **defeq-proper + infer-proper construction (25.5% combined).**
   Mostly genuinely-new terms (eta expansion, result-type assembly), so
   no inst_univ-style monolith — but nobody has audited these sites for
   ptr-reuse the way inst_univ was. Cheap to probe (extend the probe
   branch guards one level deeper), uncertain yield.

4. **whnf-proper (8.4%): stuck-spine reapplication.** Rebuilding
   `app(head, args...)` after a head whnf that changed nothing rebuilds
   and re-interns the spine. An unchanged-head short-circuit (return the
   original expr) is the same discipline as commit 1's arms.

5. **Cost-model recalibration.** The intern coefficient survived this
   round (predicted −5.8% vs measured −6.8% guest cycles), but each
   structural change erodes MAPE; refit the cost-unit coefficients and
   the shard-planner constants before the next big shard campaign, from
   the code's shard.rs constants + CLI-measured data (never a detached
   fit).

6. **Kernel-arena gaps** (smaller; whnf/defeq cycle axes, ~21%
   combined): per-delta-step same-head congruence inside the lazy-delta
   loop, cheapProj mode in delta loops, Bool.true fast path for
   decide-heavy proofs.

## Methodology gotchas (each cost us a wrong number this week)

- Interleave base/branch rounds for any wall-clock claim; single-window
  absolutes drift (a batch read 4.0s where interleaved truth was 4.5s).
- Probe builds: event counts exact, wall-clock invalid (see above).
- Scope-split every laziness lever: whole-env (trusted deps) vs closure
  (everything re-checked) vs shard-plan (owned checked, foreign
  consulted) behave differently; the bench zisk backend runs shard-plan
  for pre-cut heavy rows (`zkshards-<env>/`).
- Cycles are deterministic; guest execute wall and RSS on a shared box
  are not. Host RAM in execute mode is floor-dominated by the proving
  key's const-trees (~55 GiB) — deltas only show above the floor.

## Validation battery (per lever)

`cargo test -p ix-kernel --lib` → `lake build ix` → whole-env anon pass
parity on Init + InitStd (51,678 / 89,013, zero failures) → OOC bench
vs baseline (`ix bench run --backend ooc --env InitStd --ixe <shared>`)
→ zisk closure + shard-plan rows (`--backend zisk --mode execute`) with
a rebuilt guest ELF — the kernel compiles into it, and engine changes
need prove+verify, not execute alone, when they touch witness shape.
