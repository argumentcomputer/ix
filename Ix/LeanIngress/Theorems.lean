import Ix.LeanIngress
import IxC.Kernel.MainTheorem
import IxC.Kernel.Verify.Cached.MainC
import IxC.Kernel.Verify.Tier

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
  and every tier constant is typed in its scope (`Ix.Kernel.Tier.TypedIn`). -/

namespace Ix.LeanIngress

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
