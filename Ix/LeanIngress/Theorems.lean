import Ix.LeanIngress
import IxC.Kernel.MainTheorem
import IxC.Kernel.Verify.Cached.MainC

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
  constant of the accepted environment has `False`'s role key as its type. -/

namespace Ix.LeanIngress

universe u

/-- **The reading of an accepted Source-mode check**: the ingress succeeded
from the prelude's reader state, and the fold accepted its declarations
behind the prelude (`Frontend.preparePrelude`) at the evidence. -/
theorem checkSourceWith_reading {pre : Ix.Kernel.Reader.Prelude}
    {ev : Ix.Kernel.Evidences} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env} (h : checkSourceWith pre ev env blocks = .ok kenv) :
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
theorem checkSourceUsing_reading {prelude : Except String Ix.Kernel.Reader.Prelude}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env} (h : checkSourceUsing prelude env blocks = .ok kenv) :
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
    {kenv : Ix.Kernel.Env} (h : checkSource env blocks = .ok kenv) :
    ∃ pre decls, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified
        (sourceEvidence (Ix.Kernel.Frontend.preparePrelude pre.ix decls))
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv :=
  checkSourceUsing_reading h

/-- **Model existence** for the Source-mode check, at every prelude and
evidence. -/
theorem checkSourceWith_has_model (V : Type u) [Ix.Kernel.SetTheory V]
    {pre : Ix.Kernel.Reader.Prelude} {ev : Ix.Kernel.Evidences} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env}
    (h : checkSourceWith pre ev env blocks = .ok kenv) : Nonempty (Ix.Kernel.Model V kenv) := by
  obtain ⟨_, _, hc⟩ := checkSourceWith_reading h
  exact Ix.Kernel.model_exists V ev _ kenv hc

/-- **Model existence** for the Source-mode check. -/
theorem checkSource_has_model (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env} (h : checkSource env blocks = .ok kenv) :
    Nonempty (Ix.Kernel.Model V kenv) := by
  obtain ⟨_, _, _, _, hc⟩ := checkSource_reading h
  exact Ix.Kernel.model_exists V _ _ kenv hc

/-- **No proof of `False`** for the Source-mode check, at every prelude and
evidence: no accepted constant has `False`'s role key as its type. -/
theorem checkSourceWith_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V]
    {pre : Ix.Kernel.Reader.Prelude} {ev : Ix.Kernel.Evidences} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env}
    (h : checkSourceWith pre ev env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, hc⟩ := checkSourceWith_reading h
  exact Ix.Kernel.Cached.no_proof_of_False_cached V rfl hc

/-- **No proof of `False`** for the Source-mode check. -/
theorem checkSource_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env} (h : checkSource env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, _, _, hc⟩ := checkSource_reading h
  exact Ix.Kernel.Cached.no_proof_of_False_cached V rfl hc

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
