module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.ClaimsIO
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.BetaGate

public section

/-!
# The recomposition: `checkSoundAtP5` through the rules tier (task #305)

The five claims of `Model/Claims*.lean` at every fuel, assembled from
the bridge (`Verify/Rules/Bridge.lean`: run ⇒ derivation) and the
soundness (`Model/Rules/Sound.lean`: derivation ⇒ P currency).  Each
claim is a few lines: bridge the run, apply the soundness at the
claim's premises, identify the claim's reading with the existence
form's by `Option.some.inj`.

The recomposition — bridge ∘ soundness — IS the theorem the
declaration fold consumes, under the landed names, with the rules
tier's environment inputs (`RulesInputs`, `Model/Rules/Inputs.lean`)
as its hypothesis; `Model/Tiers.lean` above adds the run-stated
readability facts the fold's consumers read.

**The two literal rows** (`RulesInputs.nat_succ`, `.nat_op`) are
fields like the other seven, proved in `Model/NatStep.lean` from
`EnvModelM.nat_ops`/`div_mod`, which is where the content lives.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}
  {φ : Name → Nat}

/-- **The P soundness at one environment — the five claims at every
fuel.**  Recomposed from the bridge and the rules soundness; the
statement is the one the declaration fold and the install rows have
always consumed. -/
theorem checkSoundAtP5 (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : RulesInputs V m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel ∧
          InferClaimIO μ m φ fuel := by
  have hin : RulesInputs V m φ := h
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  intro fuel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d e e' Δa hrun hws hb hLb ea ea' hC hea hea' hok
    obtain ⟨-, -, ea'', hea'', hg, heq⟩ :=
      red_sound hin (whnfCore_bridge hrun) ⟨hws, hb, hLb⟩ hC hea hok
    rw [hea''] at hea'
    cases hea'
    exact ⟨hg, heq⟩
  · intro d e e' Δa hrun hws hb hLb ea ea' hC hea hea' hok
    obtain ⟨-, -, ea'', hea'', hg, heq⟩ :=
      red_sound hin (whnf_bridge hrun) ⟨hws, hb, hLb⟩ hC hea hok
    rw [hea''] at hea'
    cases hea'
    exact ⟨hg, heq⟩
  · intro d a b Δa hrun hwa hba hLa hwb hbb hLb aa ba hCa hCb haa hba' hga hgb
    exact defeq_sound hin (isDefEqCore_bridge hrun) ⟨hwa, hba, hLa⟩
      ⟨hwb, hbb, hLb⟩ hCa hCb haa hba' hga hgb
  · intro d e t Δa hrun hws hb hLb ea ta hC hea hta
    obtain ⟨-, -, ta', hta', hge, hgt, hmem⟩ :=
      infer_sound hin (inferTypeCore_bridge hrun) ⟨hws, hb, hLb⟩ hC hea
    rw [hta'] at hta
    cases hta
    exact ⟨hge, hgt, hmem⟩
  · intro d e t Δa hrun hws hb hLb ea ta hC hea hta hok
    obtain ⟨-, -, ta', hta', hgt, hmem⟩ :=
      infer_sound hin (inferTypeCoreIO_bridge hrun) ⟨hws, hb, hLb⟩ hC hea hok
    rw [hta'] at hta
    cases hta
    exact ⟨hgt, hmem⟩

/-- The four sealed claims at every fuel — the joint recomposition's
first four conjuncts, kept under the landed name so every consumer
stands verbatim. -/
theorem checkSoundAt (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : RulesInputs V m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel := fun fuel =>
  ⟨(checkSoundAtP5 hμ h fuel).1, (checkSoundAtP5 hμ h fuel).2.1,
    (checkSoundAtP5 hμ h fuel).2.2.1, (checkSoundAtP5 hμ h fuel).2.2.2.1⟩

end ConLeche.Model.Rules
