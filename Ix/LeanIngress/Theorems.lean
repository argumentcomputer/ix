import Ix.LeanIngress
import IxC.Kernel.MainTheorem
import IxC.Kernel.Verify.Cached.MainC

/-! # The theorems of the Source-mode check

`checkSource` is `leanIngress` behind the prelude, then the verified fold. What
the fold accepts has a model (`Ix.Kernel.model_exists`) at every declaration
array and every `Nat`-operation pin list, so the ingress owes nothing: these
theorems hold whatever `leanIngress` produces.

* `checkSourceWith_reading`: an accepted check is the fold's acceptance of the
  ingress's declarations behind the prelude;
* `checkSourceWith_has_model`, `checkSource_has_model`: the accepted
  environment has a model in every set theory;
* `checkSourceWith_no_proof_of_False`, `checkSource_no_proof_of_False`: no
  constant of the accepted environment has the pinned `False` as its type. -/

namespace Ix.LeanIngress

universe u

/-- **The reading of an accepted Source-mode check**: the ingress succeeded
from the prelude's reader state, and the fold accepted its declarations
behind the prelude (`Frontend.preparePrelude`). -/
theorem checkSourceWith_reading {pre : Ix.Kernel.Reader.Prelude}
    {natPins : List Ix.Kernel.NatOpPinSet} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env} (h : checkSourceWith pre natPins env blocks = .ok kenv) :
    ∃ decls, leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified natPins
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv := by
  unfold checkSourceWith prepareSource at h
  cases hi : leanIngress env blocks pre.state with
  | error e => simp [hi, bind, Except.bind, Except.mapError] at h
  | ok decls =>
    simp only [hi, Except.mapError, bind, Except.bind, pure, Except.pure] at h
    cases hc : Ix.Kernel.Cached.checkDecls .verified natPins
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) with
    | error e => simp [hc] at h
    | ok kenv' =>
      simp only [hc, Except.ok.injEq] at h
      subst h
      exact ⟨decls, rfl, hc⟩

/-- An accepted `checkSource` is `checkSourceWith` at the committed prelude and
the empty pin list. -/
theorem checkSource_with {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env} (h : checkSource env blocks = .ok kenv) :
    ∃ pre, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧ checkSourceWith pre [] env blocks = .ok kenv := by
  unfold checkSource at h
  cases hp : Ix.Kernel.Reader.builtinPrelude with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pre =>
    simp only [hp, Except.mapError, bind, Except.bind] at h
    exact ⟨pre, rfl, h⟩

/-- **Model existence** for the Source-mode check, at every prelude and pin
list. -/
theorem checkSourceWith_has_model (V : Type u) [Ix.Kernel.SetTheory V]
    {pre : Ix.Kernel.Reader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env}
    (h : checkSourceWith pre natPins env blocks = .ok kenv) : Nonempty (Ix.Kernel.Model V kenv) := by
  obtain ⟨_, _, hc⟩ := checkSourceWith_reading h
  exact Ix.Kernel.model_exists V natPins _ kenv hc

/-- **Model existence** for the Source-mode check. -/
theorem checkSource_has_model (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env} (h : checkSource env blocks = .ok kenv) :
    Nonempty (Ix.Kernel.Model V kenv) := by
  obtain ⟨_, _, hw⟩ := checkSource_with h
  exact checkSourceWith_has_model V hw

/-- **No proof of `False`** for the Source-mode check, at every prelude and
pin list: no accepted constant has the pinned `False` as its type. -/
theorem checkSourceWith_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V]
    {pre : Ix.Kernel.Reader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env}
    (h : checkSourceWith pre natPins env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False := by
  obtain ⟨_, _, hc⟩ := checkSourceWith_reading h
  exact Ix.Kernel.Cached.no_proof_of_False_cached V rfl hc

/-- **No proof of `False`** for the Source-mode check. -/
theorem checkSource_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env} (h : checkSource env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False := by
  obtain ⟨_, _, hw⟩ := checkSource_with h
  exact checkSourceWith_no_proof_of_False V hw

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

/-- info: 'Ix.LeanIngress.ingressExprs_eq_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.ingressExprs_eq_shared

/-- info: 'Ix.LeanIngress.checkSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.LeanIngress.checkSource
