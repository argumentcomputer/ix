import Ix.LeanIngress
import IxCK.Kernel.MainTheorem
import IxCK.Kernel.Verify.Cached.MainC
import IxCK.Kernel.Verify.Tier
import IxCK.Kernel.Ixon.Values
import Ix.LeanIngress.Rename

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
  (`checkSourceHinted`), which is `checkSource` with none
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

/-- **An accepted Source-mode check is a reference accept**
(`Ix.Kernel.Cached.checkDecls_refines_ref`): the pure fold at some fuel
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

/-- **The strong model** of an accepted Source-mode check
(`Ix.Kernel.Cached.StrongModel`): one witness of the fold's invariant, whose
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
(`checkSourceHinted`) as of `checkSource`. -/

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

open Ix.Kernel.Reader (CDecl CExpr CName CVal BlockRead RecCounts ReadError State)

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

/-! ## Level canonicalization and key substitution

Pure characterizations of `canonExprM`, `canonValM`, `DefMember.canon`,
`canonInfo`, `BlockRead.canon`, `Converted.canon`, and `canonDecl`, their
key-preservation and conditional idempotence properties (conditioned on the
level-canonicalizer idempotence hypothesis `hf`), and their commutation with
`substKeys` (`Converted.quotient`). -/

theorem LevelMemoInv.empty (f : KLevel → KLevel) : LevelMemoInv f {} := by
  intro k v h
  simp at h

@[local simp] theorem mapLevels_id (e : CExpr .source) : mapLevels id e = e := by
  induction e <;> simp_all [mapLevels]

theorem mapLevels_comp (g f : KLevel → KLevel) (e : CExpr .source) :
    mapLevels g (mapLevels f e) = mapLevels (g ∘ f) e := by
  induction e <;> simp_all [mapLevels, List.map_map]

theorem mapLevels_congr {f g : KLevel → KLevel} (h : ∀ l, f l = g l) (e : CExpr .source) :
    mapLevels f e = mapLevels g e := by
  have hfg : f = g := funext h
  subst hfg
  rfl

theorem mapLevels_idem {f : KLevel → KLevel} (hf : ∀ l, f (f l) = f l) (e : CExpr .source) :
    mapLevels f (mapLevels f e) = mapLevels f e := by
  rw [mapLevels_comp]
  exact mapLevels_congr hf e

theorem mapLevels_substKeys (f : KLevel → KLevel) (ρ : FiberMap) (e : CExpr .source) :
    mapLevels f (Expr.substKeys ρ e) = Expr.substKeys ρ (mapLevels f e) := by
  induction e <;> simp_all [Expr.substKeys, mapLevels]

@[local simp] theorem lamBody_mapLevels (f : KLevel → KLevel) (e : CExpr .source) :
    Ix.Kernel.Frontend.lamBody (mapLevels f e) = mapLevels f (Ix.Kernel.Frontend.lamBody e) := by
  induction e with
  | lam t b m _ ih => simpa only [Ix.Kernel.Frontend.lamBody, mapLevels] using ih
  | _ => rfl

@[local simp] theorem lamBody_substKeys (ρ : FiberMap) (e : CExpr .source) :
    Ix.Kernel.Frontend.lamBody (Expr.substKeys ρ e) =
      Expr.substKeys ρ (Ix.Kernel.Frontend.lamBody e) := by
  induction e with
  | lam t b m _ ih => simpa only [Ix.Kernel.Frontend.lamBody, Expr.substKeys] using ih
  | _ => rfl

@[local simp] theorem piTeleLen_mapLevels (f : KLevel → KLevel) (e : CExpr .source) :
    Ix.Kernel.Reader.piTeleLen (mapLevels f e) = Ix.Kernel.Reader.piTeleLen e := by
  induction e with
  | forallE t b m _ ih => simp only [Ix.Kernel.Reader.piTeleLen, mapLevels, ih]
  | _ => rfl

@[local simp] theorem piTeleLen_substKeys (ρ : FiberMap) (e : CExpr .source) :
    Ix.Kernel.Reader.piTeleLen (Expr.substKeys ρ e) = Ix.Kernel.Reader.piTeleLen e := by
  induction e with
  | forallE t b m _ ih => simp only [Ix.Kernel.Reader.piTeleLen, Expr.substKeys, ih]
  | _ => rfl

/-- Pure level canonicalization of a `ConstantVal` against its own
`levelParams`. -/
def canonVal (cv : Ix.Kernel.ConstantVal .source) : Ix.Kernel.ConstantVal .source :=
  { cv with type := mapLevels (canonLevelIn cv.levelParams) cv.type }

@[local simp] theorem canonVal_name (cv : Ix.Kernel.ConstantVal .source) :
    (canonVal cv).name = cv.name := rfl

@[local simp] theorem canonVal_levelParams (cv : Ix.Kernel.ConstantVal .source) :
    (canonVal cv).levelParams = cv.levelParams := rfl

@[local simp] theorem canonVal_type (cv : Ix.Kernel.ConstantVal .source) :
    (canonVal cv).type = mapLevels (canonLevelIn cv.levelParams) cv.type := rfl

/-- Pure level canonicalization of a recursor rule's firing discipline against
`lps`. -/
def canonRecRuleFire (lps : List Ix.Kernel.LevelParam) :
    Ix.Kernel.RecRuleFire .source → Ix.Kernel.RecRuleFire .source
  | .inert => .inert
  | .plain => .plain
  | .nested lvls pins =>
    .nested (lvls.map (canonLevelIn lps)) (pins.map (mapLevels (canonLevelIn lps)))

/-- Pure level canonicalization of a recursor rule against `lps`. -/
def canonRecRule (lps : List Ix.Kernel.LevelParam)
    (r : Ix.Kernel.RecRule .source) : Ix.Kernel.RecRule .source :=
  { r with
    fire := canonRecRuleFire lps r.fire
    rhs := mapLevels (canonLevelIn lps) r.rhs }

/-- Pure level canonicalization of a projection table against
`tbl.levelParams`. -/
def canonProjTable (tbl : Ix.Kernel.ProjTable .source) : Ix.Kernel.ProjTable .source :=
  let f := canonLevelIn tbl.levelParams
  { tbl with
    structSort := f tbl.structSort
    guards := tbl.guards.map f
    bodies := tbl.bodies.map (mapLevels f) }

@[local simp] private theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
@[local simp] private theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl
@[local simp] private theorem id_map {α β : Type} (f : α → β) (x : Id α) : (f <$> x) = f x := rfl

theorem canonExprM_run (lps : List Ix.Kernel.LevelParam) (e : CExpr .source)
    (memo : Std.HashMap (CExpr .source) (CExpr .source))
    (hm : LevelMemoInv (canonLevelIn lps) memo) :
    ((canonExprM lps e).run memo).1 = mapLevels (canonLevelIn lps) e ∧
      LevelMemoInv (canonLevelIn lps) ((canonExprM lps e).run memo).2 :=
  mapLevelsGo_spec e hm

@[local simp] theorem canonExprM_run' (lps : List Ix.Kernel.LevelParam) (e : CExpr .source) :
    (canonExprM lps e).run' {} = mapLevels (canonLevelIn lps) e :=
  (canonExprM_run lps e {} (LevelMemoInv.empty _)).1

@[local simp] theorem canonExprM_run_empty_fst (lps : List Ix.Kernel.LevelParam) (e : CExpr .source) :
    ((canonExprM lps e).run {}).1 = mapLevels (canonLevelIn lps) e :=
  (canonExprM_run lps e {} (LevelMemoInv.empty _)).1

theorem canonValM_run (cv : Ix.Kernel.ConstantVal .source)
    (memo : Std.HashMap (CExpr .source) (CExpr .source))
    (hm : LevelMemoInv (canonLevelIn cv.levelParams) memo) :
    ((canonValM cv).run memo).1 = canonVal cv ∧
      LevelMemoInv (canonLevelIn cv.levelParams) ((canonValM cv).run memo).2 := by
  unfold canonValM
  obtain ⟨h1, h2⟩ := canonExprM_run cv.levelParams cv.type memo hm
  simp only [StateT.run_bind, id_bind, StateT.run_pure, id_pure, h1]
  exact ⟨rfl, h2⟩

@[local simp] theorem canonValM_run' (cv : Ix.Kernel.ConstantVal .source) :
    (canonValM cv).run' {} = canonVal cv :=
  (canonValM_run cv {} (LevelMemoInv.empty _)).1

@[local simp] theorem canonValM_run_empty_fst (cv : Ix.Kernel.ConstantVal .source) :
    ((canonValM cv).run {}).1 = canonVal cv :=
  (canonValM_run cv {} (LevelMemoInv.empty _)).1

@[local simp] theorem canonValM_name (cv : Ix.Kernel.ConstantVal .source) :
    ((canonValM cv).run' {}).name = cv.name := by
  simp

@[local simp] theorem canonValM_levelParams (cv : Ix.Kernel.ConstantVal .source) :
    ((canonValM cv).run' {}).levelParams = cv.levelParams := by
  simp

theorem list_mapM_run_inv {σ α β : Type} (I : σ → Prop) (f : α → StateM σ β) (g : α → β)
    (hf : ∀ x s, I s → ((f x).run s).1 = g x ∧ I ((f x).run s).2) :
    ∀ (xs : List α) (s : σ), I s →
      ((xs.mapM f).run s).1 = xs.map g ∧ I ((xs.mapM f).run s).2
  | [], s, hs => ⟨rfl, hs⟩
  | x :: xs, s, hs => by
    obtain ⟨h1, hs1⟩ := hf x s hs
    obtain ⟨h2, hs2⟩ := list_mapM_run_inv I f g hf xs ((f x).run s).2 hs1
    simp only [List.mapM_cons, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
      h1, h2, List.map_cons]
    exact ⟨trivial, hs2⟩

theorem array_mapM_run_inv {σ α β : Type} (I : σ → Prop) (f : α → StateM σ β) (g : α → β)
    (hf : ∀ x s, I s → ((f x).run s).1 = g x ∧ I ((f x).run s).2)
    (xs : Array α) (s : σ) (hs : I s) :
    ((xs.mapM f).run s).1 = xs.map g ∧ I ((xs.mapM f).run s).2 := by
  rw [Array.mapM_eq_mapM_toList]
  obtain ⟨h1, h2⟩ := list_mapM_run_inv I f g hf xs.toList s hs
  simp only [StateT.run_map, id_map, h1]
  refine ⟨?_, h2⟩
  rcases xs with ⟨l⟩
  simp

@[local simp] theorem DefMember.canon_eq (m : DefMember) :
    DefMember.canon m =
      { m with
        cv := canonVal m.cv
        value := mapLevels (canonLevelIn m.cv.levelParams) m.value } := by
  unfold DefMember.canon
  obtain ⟨hcv, hm₁⟩ := canonValM_run m.cv {} (LevelMemoInv.empty _)
  obtain ⟨hval, _⟩ := canonExprM_run m.cv.levelParams m.value _ hm₁
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv, hval]

@[local simp] theorem DefMember.canon_cv_name (m : DefMember) :
    (DefMember.canon m).cv.name = m.cv.name := by
  simp

@[local simp] theorem DefMember.canon_cv_levelParams (m : DefMember) :
    (DefMember.canon m).cv.levelParams = m.cv.levelParams := by
  simp

theorem canonRecRuleM_run (lps : List Ix.Kernel.LevelParam) (r : Ix.Kernel.RecRule .source)
    (memo : Std.HashMap (CExpr .source) (CExpr .source))
    (hm : LevelMemoInv (canonLevelIn lps) memo) :
    (((do
      let fire ← match r.fire with
        | .nested lvls pins => do
          let ps ← pins.mapM (canonExprM lps)
          pure (Ix.Kernel.RecRuleFire.nested (lvls.map (canonLevelIn lps)) ps)
        | f => pure f
      return { r with rhs := ← canonExprM lps r.rhs, fire } :
        StateM (Std.HashMap (CExpr .source) (CExpr .source))
          (Ix.Kernel.RecRule .source)).run memo)).1 = canonRecRule lps r ∧
    LevelMemoInv (canonLevelIn lps)
      (((do
        let fire ← match r.fire with
          | .nested lvls pins => do
            let ps ← pins.mapM (canonExprM lps)
            pure (Ix.Kernel.RecRuleFire.nested (lvls.map (canonLevelIn lps)) ps)
          | f => pure f
        return { r with rhs := ← canonExprM lps r.rhs, fire } :
          StateM (Std.HashMap (CExpr .source) (CExpr .source))
            (Ix.Kernel.RecRule .source)).run memo)).2 := by
  rcases r with ⟨ctor, nfields, rparams, fire, rhs, k, p1, p2⟩
  cases fire with
  | inert =>
    obtain ⟨hrhs, hm'⟩ := canonExprM_run lps rhs memo hm
    simp only [StateT.run_bind, id_bind, StateT.run_pure, id_pure,
      canonRecRule, canonRecRuleFire, hrhs]
    exact ⟨trivial, hm'⟩
  | plain =>
    obtain ⟨hrhs, hm'⟩ := canonExprM_run lps rhs memo hm
    simp only [StateT.run_bind, id_bind, StateT.run_pure, id_pure,
      canonRecRule, canonRecRuleFire, hrhs]
    exact ⟨trivial, hm'⟩
  | nested lvls pins =>
    obtain ⟨hpins, hm₁⟩ := list_mapM_run_inv (LevelMemoInv (canonLevelIn lps))
      (canonExprM lps) (mapLevels (canonLevelIn lps)) (canonExprM_run lps) pins memo hm
    obtain ⟨hrhs, hm₂⟩ := canonExprM_run lps rhs _ hm₁
    simp only [StateT.run_bind, id_bind, StateT.run_pure, id_pure,
      canonRecRule, canonRecRuleFire, hpins, hrhs]
    exact ⟨trivial, hm₂⟩

@[local simp] theorem canonInfo_axiomInfo (cv : Ix.Kernel.ConstantVal .source) :
    canonInfo (.axiomInfo cv) = .axiomInfo (canonVal cv) := by
  unfold canonInfo canonInfo.go
  obtain ⟨hcv, _⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv]

@[local simp] theorem canonInfo_defnInfo (cv : Ix.Kernel.ConstantVal .source)
    (v : CExpr .source) (h : Ix.Kernel.ReducibilityHint) :
    canonInfo (.defnInfo cv v h) =
      .defnInfo (canonVal cv) (mapLevels (canonLevelIn cv.levelParams) v) h := by
  unfold canonInfo canonInfo.go
  obtain ⟨hcv, hm₁⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  obtain ⟨hv, _⟩ := canonExprM_run cv.levelParams v _ hm₁
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv, hv]

@[local simp] theorem canonInfo_thmInfo (cv : Ix.Kernel.ConstantVal .source) (v : CExpr .source) :
    canonInfo (.thmInfo cv v) =
      .thmInfo (canonVal cv) (mapLevels (canonLevelIn cv.levelParams) v) := by
  unfold canonInfo canonInfo.go
  obtain ⟨hcv, hm₁⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  obtain ⟨hv, _⟩ := canonExprM_run cv.levelParams v _ hm₁
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv, hv]

@[local simp] theorem canonInfo_indInfo (cv : Ix.Kernel.ConstantVal .source)
    (caps : Ix.Kernel.IndCaps .source) :
    canonInfo (.indInfo cv caps) = .indInfo (canonVal cv) caps := by
  unfold canonInfo canonInfo.go
  obtain ⟨hcv, _⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv]

@[local simp] theorem canonInfo_ctorInfo (cv : Ix.Kernel.ConstantVal .source) (nP nF : Nat) :
    canonInfo (.ctorInfo cv nP nF) = .ctorInfo (canonVal cv) nP nF := by
  unfold canonInfo canonInfo.go
  obtain ⟨hcv, _⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv]

@[local simp] theorem canonInfo_recInfo (cv : Ix.Kernel.ConstantVal .source) (m p : Nat)
    (rules : List (Ix.Kernel.RecRule .source)) :
    canonInfo (.recInfo cv m p rules) =
      .recInfo (canonVal cv) m p (rules.map (canonRecRule cv.levelParams)) := by
  unfold canonInfo canonInfo.go
  obtain ⟨hcv, hm₁⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  obtain ⟨hrules, _⟩ := list_mapM_run_inv (LevelMemoInv (canonLevelIn cv.levelParams))
    _ (canonRecRule cv.levelParams) (canonRecRuleM_run cv.levelParams) rules _ hm₁
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv]
  exact congrArg (Ix.Kernel.ConstantInfo.recInfo (canonVal cv) m p) hrules

@[local simp] theorem canonInfo_projInfo (tbl : Ix.Kernel.ProjTable .source) :
    canonInfo (.projInfo tbl) = .projInfo (canonProjTable tbl) := by
  unfold canonInfo canonInfo.go
  obtain ⟨hbodies, _⟩ := array_mapM_run_inv (LevelMemoInv (canonLevelIn tbl.levelParams))
    (canonExprM tbl.levelParams) (mapLevels (canonLevelIn tbl.levelParams))
    (canonExprM_run tbl.levelParams) tbl.bodies {} (LevelMemoInv.empty _)
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hbodies, canonProjTable]

@[local simp] theorem BlockRead.canon_eq (rb : BlockRead .source) :
    BlockRead.canon rb =
      { rb with
        types := rb.types.map fun (c, p, i) => (canonVal c, p, i)
        ctors := rb.ctors.map fun (c, p, f) => (canonVal c, p, f)
        recs := rb.recs.map fun (c, rc, rules) =>
          (canonVal c, rc, rules.map (canonRecRule c.levelParams)) } := by
  simp only [BlockRead.canon, canonValM_run', canonInfo_recInfo]

@[local simp] theorem canonDecl_axiomDecl (cv : Ix.Kernel.ConstantVal .source) :
    canonDecl (.axiomDecl cv) = .axiomDecl (canonVal cv) := by
  simp [canonDecl]

@[local simp] theorem canonDecl_defnDecl (cv : Ix.Kernel.ConstantVal .source) (v : CExpr .source)
    (h : Ix.Kernel.ReducibilityHint) :
    canonDecl (.defnDecl cv v h) =
      .defnDecl (canonVal cv) (mapLevels (canonLevelIn cv.levelParams) v) h := by
  unfold canonDecl
  obtain ⟨hcv, hm₁⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  obtain ⟨hv, _⟩ := canonExprM_run cv.levelParams v _ hm₁
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv, hv]

@[local simp] theorem canonDecl_thmDecl (cv : Ix.Kernel.ConstantVal .source) (v : CExpr .source) :
    canonDecl (.thmDecl cv v) =
      .thmDecl (canonVal cv) (mapLevels (canonLevelIn cv.levelParams) v) := by
  unfold canonDecl
  obtain ⟨hcv, hm₁⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  obtain ⟨hv, _⟩ := canonExprM_run cv.levelParams v _ hm₁
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv, hv]

@[local simp] theorem canonDecl_opaqueDecl (cv : Ix.Kernel.ConstantVal .source) (v : CExpr .source) :
    canonDecl (.opaqueDecl cv v) =
      .opaqueDecl (canonVal cv) (mapLevels (canonLevelIn cv.levelParams) v) := by
  unfold canonDecl
  obtain ⟨hcv, hm₁⟩ := canonValM_run cv {} (LevelMemoInv.empty _)
  obtain ⟨hv, _⟩ := canonExprM_run cv.levelParams v _ hm₁
  simp only [StateT.run'_eq, StateT.run_bind, id_bind, StateT.run_pure, id_pure,
    id_map, hcv, hv]

@[local simp] theorem canonDecl_basisDecl (k : Ix.Kernel.BasisKind) :
    canonDecl (.basisDecl k) = .basisDecl k := rfl

@[local simp] theorem canonDecl_indDecl (block : List (Ix.Kernel.ConstantInfo .source)) (nP : Nat) :
    canonDecl (.indDecl block nP) = .indDecl (block.map canonInfo) nP := rfl

@[local simp] theorem canonDecl_quotDecl (k : Ix.Kernel.QuotKind)
    (cv : Ix.Kernel.ConstantVal .source) :
    canonDecl (.quotDecl k cv) = .quotDecl k (canonVal cv) := by
  simp [canonDecl]

/-! ### Key and name preservation -/

/-- The names a converted group declares, in order. -/
def Converted.names : Converted → List (CName .source)
  | .inductive rb => BlockRead.names rb
  | .definitions ms => ms.toList.map (·.cv.name)
  | .axiom cv => [cv.name]
  | .quot _ cv => [cv.name]

@[local simp] theorem BlockRead.canon_names (rb : BlockRead .source) :
    BlockRead.names (BlockRead.canon rb) = BlockRead.names rb := by
  simp only [BlockRead.names, BlockRead.canon_eq, Array.toList_map, List.map_map,
    Function.comp_def, canonVal_name]

@[local simp] theorem Converted.canon_names (c : Converted) :
    Converted.names (Converted.canon c) = Converted.names c := by
  cases c with
  | «inductive» rb => exact BlockRead.canon_names rb
  | definitions ms =>
    simp only [Converted.canon, Converted.names, Array.toList_map, List.map_map]
    have h : ((fun m : DefMember => m.cv.name) ∘ DefMember.canon) = (·.cv.name) := by
      funext m; simp
    rw [h]
  | «axiom» cv => simp [Converted.canon, Converted.names]
  | quot k cv => simp [Converted.canon, Converted.names]

@[local simp] theorem Converted.substKeys_names (ρ : FiberMap) (c : Converted) :
    Converted.names (Converted.substKeys ρ c) = (Converted.names c).map (Key.subst ρ) := by
  cases c with
  | «inductive» rb => exact BlockRead.substKeys_names ρ rb
  | definitions ms =>
    simp only [Converted.substKeys, Converted.names, Array.toList_map, List.map_map]
    rfl
  | «axiom» cv => rfl
  | quot k cv => rfl

@[local simp] theorem Converted.quotient_names (ρ : FiberMap) (c : Converted) :
    Converted.names (Converted.quotient ρ c) = (Converted.names c).map (Key.subst ρ) := by
  rw [Converted.quotient, Converted.canon_names, Converted.substKeys_names]

/-! ### Idempotence under level-canonicalizer idempotence -/

theorem canonExprM_idem {lps : List Ix.Kernel.LevelParam}
    (hf : ∀ l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l)
    (e : CExpr .source) :
    (canonExprM lps ((canonExprM lps e).run' {})).run' {} = (canonExprM lps e).run' {} := by
  simp only [canonExprM_run', mapLevels_idem hf]

theorem canonVal_idem {cv : Ix.Kernel.ConstantVal .source}
    (hf : ∀ l, canonLevelIn cv.levelParams (canonLevelIn cv.levelParams l) =
      canonLevelIn cv.levelParams l) :
    canonVal (canonVal cv) = canonVal cv := by
  simp only [canonVal, mapLevels_idem hf]

theorem canonValM_idem {cv : Ix.Kernel.ConstantVal .source}
    (hf : ∀ l, canonLevelIn cv.levelParams (canonLevelIn cv.levelParams l) =
      canonLevelIn cv.levelParams l) :
    (canonValM ((canonValM cv).run' {})).run' {} = (canonValM cv).run' {} := by
  simp only [canonValM_run', canonVal_idem hf]

theorem DefMember.canon_idem {m : DefMember}
    (hf : ∀ l, canonLevelIn m.cv.levelParams (canonLevelIn m.cv.levelParams l) =
      canonLevelIn m.cv.levelParams l) :
    DefMember.canon (DefMember.canon m) = DefMember.canon m := by
  simp only [DefMember.canon_eq, canonVal_levelParams, canonVal_idem hf, mapLevels_idem hf]

theorem canonRecRuleFire_idem {lps : List Ix.Kernel.LevelParam}
    (hf : ∀ l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l)
    (f : Ix.Kernel.RecRuleFire .source) :
    canonRecRuleFire lps (canonRecRuleFire lps f) = canonRecRuleFire lps f := by
  cases f with
  | inert => rfl
  | plain => rfl
  | nested lvls pins =>
    simp only [canonRecRuleFire, List.map_map]
    congr 1
    · exact List.map_congr_left fun l _ => hf l
    · exact List.map_congr_left fun e _ => mapLevels_idem hf e

theorem canonRecRule_idem {lps : List Ix.Kernel.LevelParam}
    (hf : ∀ l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l)
    (r : Ix.Kernel.RecRule .source) :
    canonRecRule lps (canonRecRule lps r) = canonRecRule lps r := by
  rcases r with ⟨ctor, nfields, rparams, fire, rhs, k, p1, p2⟩
  simp only [canonRecRule, canonRecRuleFire_idem hf, mapLevels_idem hf]

theorem canonProjTable_idem {tbl : Ix.Kernel.ProjTable .source}
    (hf : ∀ l, canonLevelIn tbl.levelParams (canonLevelIn tbl.levelParams l) =
      canonLevelIn tbl.levelParams l) :
    canonProjTable (canonProjTable tbl) = canonProjTable tbl := by
  have hss : canonLevelIn tbl.levelParams (canonLevelIn tbl.levelParams tbl.structSort) =
      canonLevelIn tbl.levelParams tbl.structSort := hf tbl.structSort
  have hgs : (tbl.guards.map (canonLevelIn tbl.levelParams)).map (canonLevelIn tbl.levelParams) =
      tbl.guards.map (canonLevelIn tbl.levelParams) := by
    rw [List.map_map]
    exact List.map_congr_left fun l _ => hf l
  have hbs : (tbl.bodies.map (mapLevels (canonLevelIn tbl.levelParams))).map
      (mapLevels (canonLevelIn tbl.levelParams)) =
      tbl.bodies.map (mapLevels (canonLevelIn tbl.levelParams)) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map]
    exact List.map_congr_left fun e _ => mapLevels_idem hf e
  simp only [canonProjTable, hss, hgs, hbs]

/-- Conditional idempotence of `canonInfo`, given level-canonicalizer
idempotence `hf`. -/
theorem canonInfo_idem
    (hf : ∀ lps l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l)
    (ci : Ix.Kernel.ConstantInfo .source) :
    canonInfo (canonInfo ci) = canonInfo ci := by
  cases ci with
  | axiomInfo cv =>
    simp only [canonInfo_axiomInfo, canonVal_idem (hf cv.levelParams)]
  | defnInfo cv v h =>
    simp only [canonInfo_defnInfo, canonVal_levelParams,
      canonVal_idem (hf cv.levelParams), mapLevels_idem (hf cv.levelParams)]
  | thmInfo cv v =>
    simp only [canonInfo_thmInfo, canonVal_levelParams,
      canonVal_idem (hf cv.levelParams), mapLevels_idem (hf cv.levelParams)]
  | indInfo cv caps =>
    simp only [canonInfo_indInfo, canonVal_idem (hf cv.levelParams)]
  | ctorInfo cv nP nF =>
    simp only [canonInfo_ctorInfo, canonVal_idem (hf cv.levelParams)]
  | recInfo cv m p rules =>
    simp only [canonInfo_recInfo, canonVal_levelParams,
      canonVal_idem (hf cv.levelParams), List.map_map]
    congr 1
    exact List.map_congr_left fun r _ => canonRecRule_idem (hf cv.levelParams) r
  | projInfo tbl =>
    simp only [canonInfo_projInfo, canonProjTable_idem (hf tbl.levelParams)]

/-- Conditional idempotence of `BlockRead.canon`, given level-canonicalizer
idempotence `hf`. -/
theorem BlockRead.canon_idem
    (hf : ∀ lps l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l)
    (rb : BlockRead .source) :
    BlockRead.canon (BlockRead.canon rb) = BlockRead.canon rb := by
  have htys : (rb.types.map fun (c, p, i) => (canonVal c, p, i)).map
      (fun (c, p, i) => (canonVal c, p, i)) =
      rb.types.map fun (c, p, i) => (canonVal c, p, i) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map]
    refine List.map_congr_left fun ⟨c, p, i⟩ _ => ?_
    simp only [Function.comp_apply, canonVal_idem (hf c.levelParams)]
  have hcts : (rb.ctors.map fun (c, p, f) => (canonVal c, p, f)).map
      (fun (c, p, f) => (canonVal c, p, f)) =
      rb.ctors.map fun (c, p, f) => (canonVal c, p, f) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map]
    refine List.map_congr_left fun ⟨c, p, f⟩ _ => ?_
    simp only [Function.comp_apply, canonVal_idem (hf c.levelParams)]
  have hrs : (rb.recs.map fun (c, rc, rules) =>
      (canonVal c, rc, rules.map (canonRecRule c.levelParams))).map
      (fun (c, rc, rules) => (canonVal c, rc, rules.map (canonRecRule c.levelParams))) =
      rb.recs.map fun (c, rc, rules) =>
        (canonVal c, rc, rules.map (canonRecRule c.levelParams)) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map]
    refine List.map_congr_left fun ⟨c, rc, rules⟩ _ => ?_
    simp only [Function.comp_apply, canonVal_levelParams,
      canonVal_idem (hf c.levelParams), List.map_map]
    congr 2
    exact List.map_congr_left fun r _ => canonRecRule_idem (hf c.levelParams) r
  simp only [BlockRead.canon_eq, htys, hcts, hrs]

/-- Conditional idempotence of `Converted.canon`, given the level-canonicalizer
idempotence hypothesis `hf : ∀ lps l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l`. -/
theorem Converted.canon_idem
    (hf : ∀ lps l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l)
    (c : Converted) :
    Converted.canon (Converted.canon c) = Converted.canon c := by
  cases c with
  | «inductive» rb =>
    simp only [Converted.canon, BlockRead.canon_idem hf]
  | definitions ms =>
    simp only [Converted.canon, Array.map_map]
    congr 1
    rw [← Array.toList_inj]
    simp only [Array.toList_map]
    exact List.map_congr_left fun m _ => DefMember.canon_idem (hf m.cv.levelParams)
  | «axiom» cv =>
    simp only [Converted.canon, canonValM_run', canonVal_idem (hf cv.levelParams)]
  | quot k cv =>
    simp only [Converted.canon, canonValM_run', canonVal_idem (hf cv.levelParams)]

/-- Conditional idempotence of `canonDecl`, given the level-canonicalizer
idempotence hypothesis `hf : ∀ lps l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l`. -/
theorem canonDecl_idem
    (hf : ∀ lps l, canonLevelIn lps (canonLevelIn lps l) = canonLevelIn lps l)
    (d : CDecl .source) :
    canonDecl (canonDecl d) = canonDecl d := by
  cases d with
  | axiomDecl cv =>
    simp only [canonDecl_axiomDecl, canonVal_idem (hf cv.levelParams)]
  | defnDecl cv v h =>
    simp only [canonDecl_defnDecl, canonVal_levelParams,
      canonVal_idem (hf cv.levelParams), mapLevels_idem (hf cv.levelParams)]
  | thmDecl cv v =>
    simp only [canonDecl_thmDecl, canonVal_levelParams,
      canonVal_idem (hf cv.levelParams), mapLevels_idem (hf cv.levelParams)]
  | opaqueDecl cv v =>
    simp only [canonDecl_opaqueDecl, canonVal_levelParams,
      canonVal_idem (hf cv.levelParams), mapLevels_idem (hf cv.levelParams)]
  | basisDecl k => rfl
  | indDecl block nP =>
    simp only [canonDecl_indDecl, List.map_map]
    congr 1
    exact List.map_congr_left fun ci _ => canonInfo_idem hf ci
  | quotDecl k cv =>
    simp only [canonDecl_quotDecl, canonVal_idem (hf cv.levelParams)]

/-! ### Commutation of level canonicalization with key substitution -/

@[local simp] theorem canonExprM_substKeys (ρ : FiberMap) (lps : List Ix.Kernel.LevelParam)
    (e : CExpr .source) :
    (canonExprM lps (Expr.substKeys ρ e)).run' {} =
      Expr.substKeys ρ ((canonExprM lps e).run' {}) := by
  simp only [canonExprM_run', mapLevels_substKeys]

@[local simp] theorem canonVal_substKeys (ρ : FiberMap) (cv : Ix.Kernel.ConstantVal .source) :
    canonVal (ConstantVal.substKeys ρ cv) = ConstantVal.substKeys ρ (canonVal cv) := by
  simp only [canonVal, ConstantVal.substKeys, mapLevels_substKeys]

@[local simp] theorem canonValM_substKeys (ρ : FiberMap) (cv : Ix.Kernel.ConstantVal .source) :
    (canonValM (ConstantVal.substKeys ρ cv)).run' {} =
      ConstantVal.substKeys ρ ((canonValM cv).run' {}) := by
  simp only [canonValM_run', canonVal_substKeys]

@[local simp] theorem DefMember.canon_substKeys (ρ : FiberMap) (m : DefMember) :
    DefMember.canon (DefMember.substKeys ρ m) = DefMember.substKeys ρ (DefMember.canon m) := by
  simp only [DefMember.canon_eq, DefMember.substKeys, ConstantVal.substKeys_levelParams,
    canonVal_substKeys, mapLevels_substKeys]

@[local simp] theorem canonRecRuleFire_substKeys (ρ : FiberMap) (lps : List Ix.Kernel.LevelParam)
    (f : Ix.Kernel.RecRuleFire .source) :
    canonRecRuleFire lps (RecRuleFire.substKeys ρ f) =
      RecRuleFire.substKeys ρ (canonRecRuleFire lps f) := by
  cases f with
  | inert => rfl
  | plain => rfl
  | nested lvls pins =>
    simp only [canonRecRuleFire, RecRuleFire.substKeys, List.map_map, Function.comp_def,
      mapLevels_substKeys]

@[local simp] theorem canonRecRule_substKeys (ρ : FiberMap) (lps : List Ix.Kernel.LevelParam)
    (r : Ix.Kernel.RecRule .source) :
    canonRecRule lps (RecRule.substKeys ρ r) = RecRule.substKeys ρ (canonRecRule lps r) := by
  rcases r with ⟨ctor, nfields, rparams, fire, rhs, k, p1, p2⟩
  simp only [canonRecRule, RecRule.substKeys, canonRecRuleFire_substKeys, mapLevels_substKeys]

@[local simp] theorem canonProjTable_substKeys (ρ : FiberMap) (tbl : Ix.Kernel.ProjTable .source) :
    canonProjTable (ProjTable.substKeys ρ tbl) = ProjTable.substKeys ρ (canonProjTable tbl) := by
  have hbs : (tbl.bodies.map (Expr.substKeys ρ)).map (mapLevels (canonLevelIn tbl.levelParams)) =
      (tbl.bodies.map (mapLevels (canonLevelIn tbl.levelParams))).map (Expr.substKeys ρ) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map, Function.comp_def, mapLevels_substKeys]
  simp only [canonProjTable, ProjTable.substKeys, hbs]

@[local simp] theorem canonInfo_substKeys (ρ : FiberMap) (ci : Ix.Kernel.ConstantInfo .source) :
    canonInfo (ConstantInfo.substKeys ρ ci) = ConstantInfo.substKeys ρ (canonInfo ci) := by
  cases ci with
  | axiomInfo cv =>
    simp only [ConstantInfo.substKeys, canonInfo_axiomInfo, canonVal_substKeys]
  | defnInfo cv v h =>
    simp only [ConstantInfo.substKeys, canonInfo_defnInfo, ConstantVal.substKeys_levelParams,
      canonVal_substKeys, mapLevels_substKeys]
  | thmInfo cv v =>
    simp only [ConstantInfo.substKeys, canonInfo_thmInfo, ConstantVal.substKeys_levelParams,
      canonVal_substKeys, mapLevels_substKeys]
  | indInfo cv caps =>
    simp only [ConstantInfo.substKeys, canonInfo_indInfo, canonVal_substKeys]
  | ctorInfo cv nP nF =>
    simp only [ConstantInfo.substKeys, canonInfo_ctorInfo, canonVal_substKeys]
  | recInfo cv mI rP rules =>
    simp only [ConstantInfo.substKeys, canonInfo_recInfo, ConstantVal.substKeys_levelParams,
      canonVal_substKeys, List.map_map, Function.comp_def, canonRecRule_substKeys]
  | projInfo tbl =>
    simp only [ConstantInfo.substKeys, canonInfo_projInfo, canonProjTable_substKeys]

@[local simp] theorem BlockRead.canon_substKeys (ρ : FiberMap) (rb : BlockRead .source) :
    BlockRead.canon (BlockRead.substKeys ρ rb) = BlockRead.substKeys ρ (BlockRead.canon rb) := by
  have htys : (rb.types.map fun (cv, p, i) => (ConstantVal.substKeys ρ cv, p, i)).map
      (fun (c, p, i) => (canonVal c, p, i)) =
      (rb.types.map fun (c, p, i) => (canonVal c, p, i)).map
        fun (cv, p, i) => (ConstantVal.substKeys ρ cv, p, i) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map]
    refine List.map_congr_left fun ⟨cv, p, i⟩ _ => ?_
    simp only [Function.comp_apply, canonVal_substKeys]
  have hcts : (rb.ctors.map fun (cv, p, f) => (ConstantVal.substKeys ρ cv, p, f)).map
      (fun (c, p, f) => (canonVal c, p, f)) =
      (rb.ctors.map fun (c, p, f) => (canonVal c, p, f)).map
        fun (cv, p, f) => (ConstantVal.substKeys ρ cv, p, f) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map]
    refine List.map_congr_left fun ⟨cv, p, f⟩ _ => ?_
    simp only [Function.comp_apply, canonVal_substKeys]
  have hrs : (rb.recs.map fun (cv, rc, rules) =>
      (ConstantVal.substKeys ρ cv, rc, rules.map (RecRule.substKeys ρ))).map
      (fun (c, rc, rules) => (canonVal c, rc, rules.map (canonRecRule c.levelParams))) =
      (rb.recs.map fun (c, rc, rules) =>
        (canonVal c, rc, rules.map (canonRecRule c.levelParams))).map
        fun (cv, rc, rules) => (ConstantVal.substKeys ρ cv, rc, rules.map (RecRule.substKeys ρ)) := by
    rw [← Array.toList_inj]
    simp only [Array.toList_map, List.map_map]
    refine List.map_congr_left fun ⟨cv, rc, rules⟩ _ => ?_
    simp only [Function.comp_apply, ConstantVal.substKeys_levelParams, canonVal_substKeys,
      List.map_map, Function.comp_def, canonRecRule_substKeys]
  simp only [BlockRead.canon_eq, BlockRead.substKeys, htys, hcts, hrs]

@[local simp] theorem Converted.canon_substKeys (ρ : FiberMap) (c : Converted) :
    Converted.canon (Converted.substKeys ρ c) = Converted.substKeys ρ (Converted.canon c) := by
  cases c with
  | «inductive» rb =>
    simp only [Converted.canon, Converted.substKeys, BlockRead.canon_substKeys]
  | definitions ms =>
    simp only [Converted.canon, Converted.substKeys, Array.map_map, Function.comp_def,
      DefMember.canon_substKeys]
  | «axiom» cv =>
    simp only [Converted.canon, Converted.substKeys, canonValM_run', canonVal_substKeys]
  | quot k cv =>
    simp only [Converted.canon, Converted.substKeys, canonValM_run', canonVal_substKeys]

theorem Converted.quotient_eq_substKeys_canon (ρ : FiberMap) (c : Converted) :
    Converted.quotient ρ c = Converted.substKeys ρ (Converted.canon c) :=
  Converted.canon_substKeys ρ c

@[local simp] theorem canonDecl_substKeys (ρ : FiberMap) (d : CDecl .source) :
    canonDecl (Declaration.substKeys ρ d) = Declaration.substKeys ρ (canonDecl d) := by
  cases d with
  | axiomDecl cv =>
    simp only [Declaration.substKeys, canonDecl_axiomDecl, canonVal_substKeys]
  | defnDecl cv v h =>
    simp only [Declaration.substKeys, canonDecl_defnDecl, ConstantVal.substKeys_levelParams,
      canonVal_substKeys, mapLevels_substKeys]
  | thmDecl cv v =>
    simp only [Declaration.substKeys, canonDecl_thmDecl, ConstantVal.substKeys_levelParams,
      canonVal_substKeys, mapLevels_substKeys]
  | opaqueDecl cv v =>
    simp only [Declaration.substKeys, canonDecl_opaqueDecl, ConstantVal.substKeys_levelParams,
      canonVal_substKeys, mapLevels_substKeys]
  | basisDecl k => rfl
  | indDecl block nP =>
    simp only [Declaration.substKeys, canonDecl_indDecl, List.map_map, Function.comp_def,
      canonInfo_substKeys]
  | quotDecl k cv =>
    simp only [Declaration.substKeys, canonDecl_quotDecl, canonVal_substKeys]

@[simp] theorem Declaration.beqF_refl (d : CDecl .source) :
    Declaration.beqF d d = true := by
  rw [Declaration.beqF_eq]
  exact decide_eq_true rfl

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

/-- info: 'Ix.LeanIngress.canonDecl_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.canonDecl_idem

/-- info: 'Ix.LeanIngress.Converted.canon_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.Converted.canon_idem

/-- info: 'Ix.LeanIngress.Converted.quotient_eq_substKeys_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.Converted.quotient_eq_substKeys_canon

/-- info: 'Ix.LeanIngress.canonDecl_substKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.canonDecl_substKeys

/-- info: 'Ix.LeanIngress.Declaration.beqF_refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.Declaration.beqF_refl
