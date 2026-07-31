# Handoff: IxVM environment machine (branch `sb/aiur-machine-v2`)

Working note for whoever continues this branch — delete before merging.
Written 2026-07-31. This is the re-port of the June env-machine line
(`sb/aiur-machine`, 11 stranded commits) onto the modern
`sb/measured-ingress` kernel; of the June commits, main had already
absorbed level normalization, prim_family, flat QueryMap, and KValNode
removal — the machine itself was the missing piece.

## What this branch is

Five commits stacked on `sb/measured-ingress` (rebased onto the
post-#442-merge lineage):

1. **Environment-machine whnf** — first beta enters `mwhnf_spine`;
   subsequent betas/zetas are O(1) env pushes; substitution
   materializes only at exits (`clo_subst` readback). `Clo` carries its
   env length (the June C0 lesson: an `env_len` walk was 94M rows on
   UTF8-class); `clo_subst` has an n=0 fast path and follows the modern
   hot/cold house style (guard-entry + cold BVar/Let circuits, NOT the
   old inline-guard pattern — upstream abandoned it).
2. **Idx-keyed proj-def classification** — one memo row per constant
   instead of per delta candidate (was 12.7M rows on the UTF8 codec
   check); BOTH const-head dispatches (delta-full and no-delta) gated.
3. **Lazy closure-iota** — only the major materializes; pmm/fields/post
   ride as closures into the rule RHS. Deliberate misses to the plain
   path: K recursors, LITERAL majors (linear-rec / nat-offset /
   expansion shortcuts live there — the June port bypassed linear-rec,
   this one does not), non-ctor majors (struct-eta).
4. **Machine-native delta** — family-0 non-proj-def Defn unfolds
   re-enter the machine with the closure spine intact (zero readback
   between delta steps). The CWhnf symbolic layer, closure def-eq, and
   the plain-path capture route (`mwhnf_const_p`) were deliberately NOT
   ported — June measured ceq as barely engaging; revisit only if a
   workload demands it.
5. **FFT pin refresh** — 61/64 pins moved, ALL downward (Nat.decEq
   −3.1%, Array.append_assoc −1.3%, Vector.append −1.2%), zero
   regressions; parity/execute/IOBuffer assertions unchanged.

Design invariants honored (verify again after any edit): every machine
exit goes through the plain `whnf_const_head` / `whnf_proj_head`, so
wanted-stub reporting (ch 97/98) and consult classification (ch 96)
fire unchanged — the repair driver depends on this; `whnf_nd` (def-eq
Tier 1d) keeps eager beta because machine exits delta-unfold and would
corrupt no-delta semantics; any `Ix/IxVM/*.lean` edit requires
`ix codegen` + rebuild (FunIdx desync ⇒ phantom InvalidIOKey).

## Remaining todos, in order

1. **The monster-set benchmark that decides the merge.** The suite pins
   only certify small fixtures. Run the acceptance measurement against
   the measured-ingress base binary: whole-closure `ix check --ixe`
   FFT on `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual`
   (28B-step class), the `Vector/Array.extract_append` proof family,
   `Int16/Int64.instRxcHasSize_eq`, `List.mergeSort`, plus the
   foldAdd/natreclinear curried-sharing sentinels (June regression
   class: IxVM Phase A cost +14.7% on foldAdd_2000; mitigation if it
   bites = env readback trimming or tighter entry gate). June reference
   wins: Int16 −34%, Vector −17..−25%. Bar: ≥1% FFT or RAM benefit on
   the suite, per-phase ablation if the cumulative number is ambiguous
   (rebuild at each commit).
2. **Init repair E2E** (`ix check --ixe Init.ixe --ixes --repair`):
   replay divergence rate WILL shift — the machine changes the Aiur
   kernel's cache discipline, the exact axis the escalation ladder
   absorbs. Expect green with ≤ a few targeted escalations; a frontier
   round appearing where none was needed = investigate before merging.
3. **Shard-scale RAM measurement** — the June sweep's headline was that
   the machine let the bitblast monster COMPLETE where the baseline
   guest crashed; here the analog is prove-side record/trace volume.
   Re-run the head-shard proves (`ix prove --ixe Init.ixe --ixes`) and
   compare peak RSS vs the measured-ingress baselines (142.7–189.0 GiB
   head-5 scatter). Trace volume ∝ FFT, so wins concentrate on
   reduction-heavy shards.
4. **If UTF8-class shard content matters**: the ported slice does not
   include the capture route (plain-path Const heads entering the
   machine for delta chains) or CWhnf symbolic values — June's C1.5
   probe showed the readback complex collapsing 44%→16.5% of entries
   with them. Take them up only with a UTF8-class workload in hand and
   the June `04c6901` diff as reference.
5. **Rust-side native delta feeds back here** — the OOC/Zisk handoff
   (`sb/inst-univ-memo`'s HANDOFF.md) ranks machine-native delta at the
   Rust whnf layer as the top remaining kernel win; this branch's
   `mwhnf_const` Defn arm is its working blueprint. Whoever does that
   port should keep the two implementations' miss tables aligned, or
   recorder/replayer divergence (item 2's axis) grows.

## Validation battery

`ix codegen` (+ commit the regenerated `crates/ixvm-codegen/src/
aiur_ixvm.rs`) → `lake build ix` → `lake test -- ixvm --ignored`
(the FULL gated suite — plain `lake test` skips the pins and parity;
CI's nextest runs ignored tests, so never gate a test with an
env-var `expect()`) → refresh pins if they moved → repair E2E (item 2).
