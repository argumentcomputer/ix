# Reduction-mechanics graft onto PR 562

Goal: recover the 22–44% wall regression of 562-as-merged vs `caebde6`
(init 75.9s vs 52.8s, initstd 1:58.8 vs 1:37.5) while preserving 562's
correctness properties (bounded lazy def-eq, open-Nat compactness, the
Mathlib detonator at ~100s). Non-goals: touching `whnf_struct_core`
internals, changing def-eq tier policy, or any micro-optimization
without census evidence.

## Piece A — (head, spine)-space fire paths

Every reduction helper that "fires" returns `(status, head, spine)`
instead of a materialized application:

- status 0 = miss (`BVar0` filler, `Nil`)
- status 1 = re-reduce: caller re-enters ITS OWN reducer's
  `whnf_with_spine` / `whnf_nd_with_spine` with the head and spine
- status 2 = canonical stuck form (materialized expr, `Nil`): caller
  returns it, NEVER re-reduces (existing invariant, unchanged)

Converted helpers: `try_iota`, `try_k_synth_iota`,
`try_struct_eta_iota`, `try_quot_lift`/`try_quot_ind` (+
`try_quot_iota` pass-through), `try_reduce_projection_definition`,
`try_reduce_fin_val_decidable_rec`.

Callers (both reducers): const-head Defn/proj-def, Quot, Rec K-arm
(`(0, head)` filler gains a `Nil` third slot), Rec iota arm, struct-eta
fallback; proj-head fin-val hook re-enters with
`list_concat(inner_post, outer_spine)`.

Fire sites build spines with tail-sharing `list_concat(new, post)` —
cons-list concat copies only the new prefix — so a reduction step costs
O(args consumed) instead of three full-spine `apply_spine`
materializations plus a full `collect_spine` re-walk. Measured on the
detonator (pre-562): `expr_inst_many_walk` 86M → 2.4M queries.

562 interactions, checked against their diff:
- Their Whnf change is additive (+95/−1): all graft sites are
  byte-identical to pre-f7474ec main. The f7474ec edit script largely
  re-applies; divergences are re-derived by hand.
- `whnf_struct_core*` (their new Tier-4c structural reducer) does not
  route through the try_* family — no protocol change. Verify by grep
  at graft time.
- Their DefEq's three credit-bounded `apply_spine` delta steps are out
  of scope (bounded by credit 8, validated).
- Their open-Nat dispatcher gate is untouched by A.

The Aiur DSL typechecker is the migration checklist: any missed
tuple-arity site fails `lake build` (observed in the failed auto-merge).

## Piece B — inline closed-body lbr gates

At `whnf_apply_beta` (both reducers) and the `Let` arms (both
reducers): gate `expr_inst1`/`expr_inst_many` behind
`memo_u32_less_than(0, expr_lbr(body))` — a body with no loose bvars
needs no substitution and no shift, and gating BEFORE the call avoids
minting an `(e, substs, depth)` query per fresh environment
(constant-function betas were ~99% of the detonator's dispatcher map).
Mirrors tc.rs `instantiate_rev`'s `lbr <= depth` fast path.

Optional site, pending code read: if `whnf_struct_core` carries its own
beta arm, the same two-line gate applies there (cheapens def-eq Tier
4c). Apply only if the arm exists and is shaped identically.

## Known churn: test pins

Skipping intermediate `apply_spine` materialization means intermediate
App nodes are never `store_cc`'d — memory-map unique counts shrink, so
witness row counts and FFT pins (Tests/Main, kernelCheckEntries
expectations, re-pinned by 562) MAY shift again. This is expected and
strictly-good churn (fewer intermediate nodes = smaller witness);
re-pin with that justification. Plan-mode manifests may likewise show
slightly smaller raws.

## Sequencing

1. Land the hugepage keep/delete verdict first (4K A/B in flight), so
   the graft baseline is final.
2. Merge current `sb/aiur-concurrent-record` (arena redesign) into
   `test-pr562-merge`; only the generated kernel conflicts — regen
   resolves it.
3. Apply B (tiny) → regen → detonator quick-check (must stay ~100s).
4. Apply A → regen → full gates.
5. Gates, in order: aiur cargo suite; Lean test pins (re-pin if
   shifted, documented); detonator solo ≤ ~2 min; init-8k zero-rejects
   smoke; same-hour 3-way A/B (HEAD vs 562-merge vs 562+graft) on
   init + initstd + lean.
6. Decision rule: combined kernel must clearly beat plain 562 AND land
   within ~5% of HEAD (or better). Residual gap ⇒ run
   IX_EXEC_DUMP_COUNTS census on the combined kernel before any
   further mechanics — no unmeasured optimization.
7. Then: Mathlib plan+verify (campaign completion); offer the graft
   upstream as a follow-up PR to 562.

## Explicitly deferred (need census evidence first)

- O(1) spine lengths threaded through `peel_beta` (kills `list_length`
  walks) — detonator-census volume, unproven on healthy envs.
- Array-ish subst lookup (`list_lookup` is O(ofs) per bvar hit).
- Any change to their bounded-def-eq credit machinery.
