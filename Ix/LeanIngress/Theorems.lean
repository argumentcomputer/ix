import Ix.LeanIngress
import IxC.Kernel.MainTheorem
import IxC.Kernel.Verify.Cached.MainC
import IxC.Kernel.Verify.Tier
import IxC.Kernel.Ixon.Values

/-! # The theorems of the Source-mode check

`checkSource` is `leanIngress` behind the prelude, then the verified fold at
Source mode's evidence. What the fold accepts has a model
(`Ix.Kernel.model_exists`) at every declaration array and every evidence, so
the ingress and the evidence owe nothing: these theorems hold whatever
`leanIngress` and `sourceEvidence` produce.

* `checkSourceWith_reading`, `checkSource_reading`: an accepted check is the
  fold's acceptance of the ingress's declarations behind the prelude;
* `checkSourceWith_has_model`, `checkSource_has_model`: the accepted
  environment has a model in every set theory;
* `checkSourceWith_no_proof_of_False`, `checkSource_no_proof_of_False`: no
  constant of the accepted environment has `False`'s role key as its type.
* `checkSourceTieredUsing_ok`, `checkSourceTiered_has_model`,
  `checkSourceTiered_typed`: the tiered check (`checkSourceTiered`) accepts
  the logical declarations exactly as `checkSource` would, its logical
  environment has a model, is well formed and misses every tier constant,
  and every tier constant is typed in its scope (`Ix.Kernel.Tier.TypedIn`).
* `checkSource_refines_ref`: an accepted check is a reference accept (the
  pure fold at some fuel), `Ix.Kernel.Cached.AcceptsRef`;
* `checkSource_strongModel`, `checkSource_model_values`: the strong model
  (`Ix.Kernel.Cached.StrongModel`, one witness of the fold's invariant) and
  a model with the value clauses (definitions denote their values, values
  read only their own level parameters);
* `checkSourceHinted_reading`, `checkSourceHinted_refines_ref`,
  `checkSourceHinted_strongModel`, `checkSourceHinted_model_values`,
  `checkSourceHinted_no_proof_of_False`: the same at hint overrides
  (`checkSourceHinted`, Route A's B7), which is `checkSource` with none
  (`checkSourceHinted_none`);
* `orderOf_complete`, `scheduleOf_complete`, `leanIngress_converts`,
  `checkSource_converts`: every group is in the order and scheduled, so an
  accepted check converted every group of its environment (coverage, not
  soundness: it says what Source acceptance establishes about the ingress). -/

namespace Ix.LeanIngress

/-! Source mode's binding (`sourceBinding`), checked: every role's Lean name
keys that role, and the name map holds the roles' names and nothing else.
(Here rather than beside `sourceBinding`: `Ix.LeanIngress` is a `module`, whose
`#guard`s would need `meta` imports.) -/

#guard Ix.Kernel.Role.all.all fun r => (Ix.Kernel.Key.ofName r.leanName == .role r : Bool)
#guard Ix.Kernel.Role.byLeanName.size == Ix.Kernel.Role.all.length

universe u

/-- **The reading of an accepted Source-mode check**: the ingress succeeded
from the prelude's reader state, and the fold accepted its declarations
behind the prelude (`Frontend.preparePrelude`) at the evidence. -/
theorem checkSourceWith_reading {pre : Ix.Kernel.Reader.Prelude .source}
    {ev : Ix.Kernel.Evidences .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (h : checkSourceWith pre ev env blocks = .ok kenv) :
    ∃ decls, leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified ev
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv := by
  unfold checkSourceWith prepareSource at h
  cases hi : leanIngress env blocks pre.state with
  | error e => simp [hi, bind, Except.bind, Except.mapError] at h
  | ok decls =>
    simp only [hi, Except.mapError, bind, Except.bind, pure, Except.pure] at h
    cases hc : Ix.Kernel.Cached.checkDecls .verified ev
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) with
    | error e => simp [hc] at h
    | ok kenv' =>
      simp only [hc, Except.ok.injEq] at h
      subst h
      exact ⟨decls, rfl, hc⟩

/-- The reading of an accepted `checkSourceUsing`, at any prelude source. -/
theorem checkSourceUsing_reading {prelude : Except String (Ix.Kernel.Reader.Prelude .source)}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (h : checkSourceUsing prelude env blocks = .ok kenv) :
    ∃ pre decls, prelude = .ok pre ∧
      leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv := by
  unfold checkSourceUsing prepareSource at h
  cases hp : prelude with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pre =>
    cases hi : leanIngress env blocks pre.state with
    | error e => simp [hp, hi, bind, Except.bind, Except.mapError] at h
    | ok decls =>
      simp only [hp, hi, Except.mapError, bind, Except.bind, pure, Except.pure] at h
      cases hc : Ix.Kernel.Cached.checkDecls .verified
          (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
          (Ix.Kernel.Frontend.preparePrelude pre.ix decls) with
      | error e => simp [hc] at h
      | ok kenv' =>
        simp only [hc, Except.ok.injEq] at h
        subst h
        exact ⟨pre, decls, rfl, hi, hc⟩

/-- **The reading of an accepted `checkSource`**: the committed prelude, the
ingress's declarations behind it, and the fold's acceptance of them at
Source mode's evidence over them. -/
theorem checkSource_reading {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (h : checkSource env blocks = .ok kenv) :
    ∃ pre decls, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv :=
  checkSourceUsing_reading h

/-- **Model existence** for the Source-mode check, at every prelude and
evidence. -/
theorem checkSourceWith_has_model (V : Type u) [Ix.Kernel.SetTheory V]
    {pre : Ix.Kernel.Reader.Prelude .source} {ev : Ix.Kernel.Evidences .source} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceWith pre ev env blocks = .ok kenv) : Nonempty (Ix.Kernel.Model V kenv) := by
  obtain ⟨_, _, hc⟩ := checkSourceWith_reading h
  exact Ix.Kernel.model_exists V ev _ kenv hc

/-- **An accepted Source-mode check is a reference accept** (step 7,
`Ix.Kernel.Cached.checkDecls_refines_ref`): the pure fold at some fuel
accepts the ingress's declarations behind the prelude, at Source mode's
evidence, with the same environment. -/
theorem checkSource_refines_ref (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source} (h : checkSource env blocks = .ok kenv) :
    ∃ pre decls, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.AcceptsRef .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList kenv := by
  obtain ⟨pre, decls, hp, hi, hc⟩ := checkSource_reading h
  exact ⟨pre, decls, hp, hi, Ix.Kernel.Cached.checkDecls_refines_ref V rfl hc⟩

/-- **The strong model** of an accepted Source-mode check (step 7.2,
`Ix.Kernel.Cached.StrongModel`): one witness of the fold's invariant, whose
public model satisfies the value clauses. -/
theorem checkSource_strongModel (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source} (h : checkSource env blocks = .ok kenv) :
    Nonempty (Ix.Kernel.Cached.StrongModel V kenv) := by
  obtain ⟨_, _, _, _, hc⟩ := checkSource_reading h
  exact Ix.Kernel.Cached.checkDecls_strongModel V hc

/-- **Model existence with the value clauses** for the Source-mode check:
definitions denote their values, and values read only their own level
parameters. -/
theorem checkSource_model_values (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source} (h : checkSource env blocks = .ok kenv) :
    ∃ M : Ix.Kernel.Model V kenv, Ix.Kernel.Cached.ValueClauses M := by
  obtain ⟨_, _, _, _, hc⟩ := checkSource_reading h
  exact Ix.Kernel.Cached.checkDecls_model_values V hc

/-! ### At hint overrides

The fold's theorems hold at every hint, so they hold of the hinted check
(`checkSourceHinted`, Route A's B7) as of `checkSource`. -/

/-- The reading of an accepted hinted check, at any prelude source. -/
theorem checkSourceHintedUsing_reading {prelude : Except String (Ix.Kernel.Reader.Prelude .source)}
    {hints : Ix.Kernel.Key .source → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceHintedUsing prelude hints env blocks = .ok kenv) :
    ∃ pre decls, prelude = .ok pre ∧
      leanIngressHinted hints env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv := by
  unfold checkSourceHintedUsing prepareSourceHinted at h
  cases hp : prelude with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pre =>
    cases hi : leanIngressHinted hints env blocks pre.state with
    | error e => simp [hp, hi, bind, Except.bind, Except.mapError] at h
    | ok decls =>
      simp only [hp, hi, Except.mapError, bind, Except.bind, pure, Except.pure] at h
      cases hc : Ix.Kernel.Cached.checkDecls .verified
          (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
          (Ix.Kernel.Frontend.preparePrelude pre.ix decls) with
      | error e => simp [hc] at h
      | ok kenv' =>
        simp only [hc, Except.ok.injEq] at h
        subst h
        exact ⟨pre, decls, rfl, hi, hc⟩

/-- The reading of an accepted hinted check: the committed prelude, the
hinted ingress's declarations behind it, and the fold's acceptance of them. -/
theorem checkSourceHinted_reading {hints : Ix.Kernel.Key .source → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceHinted hints env blocks = .ok kenv) :
    ∃ pre decls, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      leanIngressHinted hints env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv :=
  checkSourceHintedUsing_reading h

/-- **An accepted hinted check is a reference accept.** -/
theorem checkSourceHinted_refines_ref (V : Type u) [Ix.Kernel.SetTheory V]
    {hints : Ix.Kernel.Key .source → Option Ix.Kernel.ReducibilityHint} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceHinted hints env blocks = .ok kenv) :
    ∃ pre decls, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      leanIngressHinted hints env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.AcceptsRef .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList kenv := by
  obtain ⟨pre, decls, hp, hi, hc⟩ := checkSourceHinted_reading h
  exact ⟨pre, decls, hp, hi, Ix.Kernel.Cached.checkDecls_refines_ref V rfl hc⟩

/-- **The strong model** of an accepted hinted check. -/
theorem checkSourceHinted_strongModel (V : Type u) [Ix.Kernel.SetTheory V]
    {hints : Ix.Kernel.Key .source → Option Ix.Kernel.ReducibilityHint} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceHinted hints env blocks = .ok kenv) :
    Nonempty (Ix.Kernel.Cached.StrongModel V kenv) := by
  obtain ⟨_, _, _, _, hc⟩ := checkSourceHinted_reading h
  exact Ix.Kernel.Cached.checkDecls_strongModel V hc

/-- **Model existence with the value clauses** for the hinted check. -/
theorem checkSourceHinted_model_values (V : Type u) [Ix.Kernel.SetTheory V]
    {hints : Ix.Kernel.Key .source → Option Ix.Kernel.ReducibilityHint} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceHinted hints env blocks = .ok kenv) :
    ∃ M : Ix.Kernel.Model V kenv, Ix.Kernel.Cached.ValueClauses M := by
  obtain ⟨_, _, _, _, hc⟩ := checkSourceHinted_reading h
  exact Ix.Kernel.Cached.checkDecls_model_values V hc

/-- **No proof of `False`** for the hinted check. -/
theorem checkSourceHinted_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V]
    {hints : Ix.Kernel.Key .source → Option Ix.Kernel.ReducibilityHint} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceHinted hints env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, _, _, hc⟩ := checkSourceHinted_reading h
  exact Ix.Kernel.Cached.no_proof_of_False_cached V rfl hc

/-- **Model existence** for the Source-mode check. -/
theorem checkSource_has_model (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source} (h : checkSource env blocks = .ok kenv) :
    Nonempty (Ix.Kernel.Model V kenv) := by
  obtain ⟨_, _, _, _, hc⟩ := checkSource_reading h
  exact Ix.Kernel.model_exists V _ _ kenv hc

/-- **No proof of `False`** for the Source-mode check, at every prelude and
evidence: no accepted constant has `False`'s role key as its type. -/
theorem checkSourceWith_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V]
    {pre : Ix.Kernel.Reader.Prelude .source} {ev : Ix.Kernel.Evidences .source} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceWith pre ev env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, hc⟩ := checkSourceWith_reading h
  exact Ix.Kernel.Cached.no_proof_of_False_cached V rfl hc

/-- **No proof of `False`** for the Source-mode check. -/
theorem checkSource_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source} (h : checkSource env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, _, _, hc⟩ := checkSource_reading h
  exact Ix.Kernel.Cached.no_proof_of_False_cached V rfl hc

/-! ## The tiered check -/

/-- **The reading of an accepted tiered check**: the prelude, the tiered
ingress of the environment's graph, the fold's accept of the logical
declarations behind the prelude at Source mode's evidence (so every theorem
about that accept applies), the logical environment well formed and missing
every tier constant, and every tier constant typed in its scope over the
tier groups' conversions. -/
theorem checkSourceTieredUsing_ok (V : Type u) [Ix.Kernel.SetTheory V]
    {prelude : Except String (Ix.Kernel.Reader.Prelude .source)} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    {ts : List (Ix.Kernel.Tier.TierConst .source)}
    (h : checkSourceTieredUsing prelude env blocks = .ok (kenv, ts)) :
    ∃ pre decls tier, prelude = .ok pre ∧
      leanIngressTieredOf (graph env blocks) pre.state = .ok (decls, tier) ∧
      Ix.Kernel.Cached.checkDecls .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv ∧
      Ix.Kernel.EnvWF kenv ∧ (∀ c ∈ ts, kenv.find? c.cv.name = none) ∧
      ∀ c ∈ ts, Ix.Kernel.Tier.TypedIn kenv tier.toList ts c := by
  unfold checkSourceTieredUsing at h
  cases hp : prelude with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pre =>
  simp only [hp, bind, Except.bind, Except.mapError] at h
  cases hf : sourceFenceOf (graph env blocks) with
  | some x => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
  | none =>
  simp only [hf, pure, Except.pure] at h
  cases hi : leanIngressTieredOf (graph env blocks) pre.state with
  | error e => simp [hi] at h
  | ok r =>
  obtain ⟨decls, tier⟩ := r
  simp only [hi] at h
  cases hc : Ix.Kernel.Cached.checkDecls .verified
      (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls) with
  | error e => simp [hc] at h
  | ok kenv' =>
  simp only [hc] at h
  cases ht : Ix.Kernel.Tier.checkTierC (Ix.Kernel.mkFEnv kenv') tier.toList with
  | error e => simp [ht, throw, throwThe, MonadExceptOf.throw] at h
  | ok r =>
  obtain ⟨fe', ts'⟩ := r
  simp only [ht, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hwf, hfresh, -, htyped⟩ := Ix.Kernel.Tier.checkDecls_checkTierC V hc ht
  exact ⟨pre, decls, tier, rfl, hi, hc, hwf, hfresh, htyped⟩

/-- **Model existence** for the tiered check's logical environment. -/
theorem checkSourceTiered_has_model (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    {ts : List (Ix.Kernel.Tier.TierConst .source)}
    (h : checkSourceTiered env blocks = .ok (kenv, ts)) : Nonempty (Ix.Kernel.Model V kenv) := by
  obtain ⟨_, _, _, _, _, hc, _⟩ := checkSourceTieredUsing_ok V h
  exact Ix.Kernel.model_exists V _ _ kenv hc

/-- **The tier of the tiered check**: the logical environment is well formed
and misses every tier constant, and every tier constant is typed in its
scope. -/
theorem checkSourceTiered_typed (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    {ts : List (Ix.Kernel.Tier.TierConst .source)}
    (h : checkSourceTiered env blocks = .ok (kenv, ts)) :
    Ix.Kernel.EnvWF kenv ∧ (∀ c ∈ ts, kenv.find? c.cv.name = none) ∧
      ∃ tds : List (Ix.Kernel.Tier.TierDecl .source), ∀ c ∈ ts, Ix.Kernel.Tier.TypedIn kenv tds ts c := by
  obtain ⟨_, _, tier, _, _, _, hwf, hfresh, htyped⟩ := checkSourceTieredUsing_ok V h
  exact ⟨hwf, hfresh, _, htyped⟩

open Ix.Kernel.Reader (CDecl ReadError State)

/-! ## Coverage: every group is scheduled

The order is a structural walk (`Ix.LeanIngress.Order`), so every group of
the graph is in it (`orderOf_complete`) and is scheduled
(`scheduleOf_complete`), with its own conversion (`scheduleOf_converted`). A
successful ingress lowered every scheduled item (`lowerAll_ok`), so it
converted every group of its environment (`leanIngress_converts`), and so
did an accepted Source-mode check (`checkSource_converts`). -/

/-- **Every group is in the order.** -/
theorem orderOf_complete (g : Graph) {i : Nat} (hi : i < g.groups.size) : i ∈ orderOf g :=
  Order.mem_dfs_of_array _ _ _ hi

/-- **Every group is scheduled.** -/
theorem scheduleOf_complete (g : Graph) {i : Nat} (hi : i < g.groups.size) :
    ∃ c, (i, c) ∈ scheduleOf g := by
  unfold scheduleOf
  exact ⟨_, Array.mem_map_of_mem (orderOf_complete g hi)⟩

/-- A scheduled group that the schedule lets through is its own conversion's
result. -/
theorem scheduleOf_converted {g : Graph} {i : Nat} {c : Except ReadError Converted}
    (h : (i, c) ∈ scheduleOf g) {conv : Converted} (ok : c = .ok conv) :
    g.converted[i]! = .ok conv := by
  unfold scheduleOf at h
  obtain ⟨j, _, e⟩ := Array.mem_map.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  cases hc : g.converted[j]! with
  | error err => simp [hc, bind, Except.bind] at ok
  | ok v =>
    simp only [hc, bind, Except.bind] at ok
    split at ok
    · cases ok
    · split at ok
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        rw [ok]
      · cases ok

/-- A loop in `Except` that only yields, run to success over `l`, ran every
element's step to success. -/
theorem forIn_ok_each {α σ ε : Type} (P : α → Prop) {f : α → σ → Except ε (ForInStep σ)}
    (hf : ∀ a b s, f a b = .ok s → P a ∧ ∃ b', s = .yield b') :
    ∀ (l : List α) (b r : σ), forIn l b f = .ok r → ∀ a ∈ l, P a := by
  intro l
  induction l with
  | nil => intro _ _ _ a h; cases h
  | cons x l ih =>
    intro b r h a ha
    rw [List.forIn_cons] at h
    cases hx : f x b with
    | error e => simp [hx, bind, Except.bind] at h
    | ok s =>
      obtain ⟨px, b', rfl⟩ := hf x b s hx
      simp only [hx, bind, Except.bind] at h
      rcases List.mem_cons.mp ha with e | e
      · subst e; exact px
      · exact ih b' r h a e

/-- **A successful lowering ran every scheduled item**: each was let through
by the schedule. -/
theorem lowerAll_ok {st : State .source} {g : Graph} {sched : Array (Nat × Except ReadError Converted)}
    {r : State .source × Array (CDecl .source)} (h : lowerAll st g sched = .ok r) :
    ∀ p ∈ sched, ∃ conv, p.2 = .ok conv := by
  unfold lowerAll at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i r' hr
    rw [← Array.forIn_toList] at hr
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hp
    have each := forIn_ok_each (fun (x : (Nat × Except ReadError Converted) × Nat) =>
        ∃ conv, x.1.2 = .ok conv) ?_ _ _ _ hr (sched[k], k)
      (by rw [Array.toList_zipIdx]; exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]))
    · exact each
    · intro a b s hs
      obtain ⟨⟨gi, c⟩, i⟩ := a
      cases c with
      | error e => simp [Except.mapError] at hs
      | ok conv =>
        refine ⟨⟨conv, rfl⟩, ?_⟩
        simp only [Except.mapError] at hs
        split at hs
        · cases hs
        · cases hs; exact ⟨_, rfl⟩

/-- **A successful ingress converted every group** of the environment's
graph. -/
theorem leanIngress_converts {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {st : State .source} {decls : Array (CDecl .source)} (h : leanIngress env blocks st = .ok decls)
    {i : Nat} (hi : i < (graph env blocks).groups.size) :
    ∃ conv, (graph env blocks).converted[i]! = .ok conv := by
  unfold leanIngress at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i r hr
    obtain ⟨c, hc⟩ := scheduleOf_complete _ hi
    obtain ⟨conv, ok⟩ := lowerAll_ok hr _ hc
    exact ⟨conv, scheduleOf_converted hc ok⟩

theorem graph_groups (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    (graph env blocks).groups = groupsOf env blocks := rfl

theorem graph_converted (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    (graph env blocks).converted = (groupsOf env blocks).map convert := rfl

/-- **An accepted Source-mode check converted every group** of its
environment (`groupsOf`): in particular every inductive block's group passes
`convertInductive`'s checks. -/
theorem checkSource_converts {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (h : checkSource env blocks = .ok kenv) :
    ∀ grp ∈ groupsOf env blocks, ∃ conv, convert grp = .ok conv := by
  obtain ⟨pre, decls, _, hi, _⟩ := checkSource_reading h
  intro grp hg
  obtain ⟨i, hlt, rfl⟩ := Array.getElem_of_mem hg
  have hi' : i < (graph env blocks).groups.size := by rw [graph_groups]; exact hlt
  obtain ⟨conv, hc⟩ := leanIngress_converts hi hi'
  have same : (graph env blocks).converted[i]! = convert (groupsOf env blocks)[i] := by
    rw [graph_converted]
    simp [hlt]
    rfl
  exact ⟨conv, same ▸ hc⟩

end Ix.LeanIngress

/-! ## Axioms

The theorems, the `@[csimp]` equation behind the compiled term conversion, and
the entry itself stand on the three standard axioms; a change of the set fails
the build. -/

/-- info: 'Ix.LeanIngress.checkSource_has_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource_has_model

/-- info: 'Ix.LeanIngress.checkSource_no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource_no_proof_of_False

/-- info: 'Ix.LeanIngress.checkSourceWith_has_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceWith_has_model

/-- info: 'Ix.LeanIngress.checkSourceWith_no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceWith_no_proof_of_False

/-- info: 'Ix.LeanIngress.checkSourceWith_reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceWith_reading

/-- info: 'Ix.LeanIngress.checkSource_reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource_reading

/-- info: 'Ix.LeanIngress.ingressExprs_eq_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.ingressExprs_eq_shared

/-- info: 'Ix.LeanIngress.checkSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource

/-- info: 'Ix.LeanIngress.checkSourceTieredUsing_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceTieredUsing_ok

/-- info: 'Ix.LeanIngress.checkSourceTiered_has_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceTiered_has_model

/-- info: 'Ix.LeanIngress.checkSourceTiered_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceTiered_typed

/-- info: 'Ix.LeanIngress.checkSourceTiered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceTiered

/-- info: 'Ix.LeanIngress.orderOf_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.orderOf_complete

/-- info: 'Ix.LeanIngress.checkSource_converts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource_converts

/-- info: 'Ix.LeanIngress.checkSource_refines_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource_refines_ref

/-- info: 'Ix.LeanIngress.checkSource_strongModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource_strongModel

/-- info: 'Ix.LeanIngress.checkSource_model_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource_model_values

/-- info: 'Ix.LeanIngress.checkSourceHinted_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceHinted_none

/-- info: 'Ix.LeanIngress.checkSourceHinted_refines_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceHinted_refines_ref

/-- info: 'Ix.LeanIngress.checkSourceHinted_model_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceHinted_model_values

/-- info: 'Ix.LeanIngress.checkSourceHinted_no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSourceHinted_no_proof_of_False

/-- info: 'Ix.LeanIngress.mapLevelsList_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.mapLevelsList_eq_fast
