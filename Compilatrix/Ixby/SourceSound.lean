import Compilatrix.Ixby.Source

namespace Compilatrix.Pipeline.ValidatedErasure

open Ixon (Address Constant)

def rawCtx {constants main config fuel}
    (erasure : ValidatedErasure constants main config fuel) : IxIR0.Ctx :=
  { env := IxIR0.Env.ofList erasure.erasure.result.raw }

/-- The backend-independent erasure prefix retains the existing Ixon → IxIR₀
simulation. Sharing well-formedness is the same source premise as before. -/
theorem sourcePreservation {constants : List (Address × Constant)} {main config eraseFuel}
    (erasure : ValidatedErasure constants main config eraseFuel)
    {fuel : Nat} {value : Ixon.Eval.Value}
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (evaluated : Ixon.Eval.eval (validatedEvalCtx constants config) fuel
      (validatedMainFrame main) [] validatedMainSource = .ok value) :
    ∃ targetFuel targetValue,
      IxIR0.eval erasure.rawCtx targetFuel [] (.ref main) = .ok targetValue ∧
      @Sim.InlinedValRel (validatedEvalCtx constants config) erasure.rawCtx
        value targetValue erasure.memberScope := by
  letI : Sim.MemberScope := erasure.memberScope
  have frameWF : (validatedMainFrame main).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [validatedMainFrame] at found
  have below : Ixon.Sharing.sharesBelow 0 validatedMainSource = true := rfl
  have inlined := Ixon.Eval.eval_inlineSharing contextWF frameWF .nil below evaluated
  have related := erasure.entry.related
  rw [EraseValidator.inlineTables_tablesOfFrame] at related
  have oracles : Sim.OracleRel (validatedEvalCtx constants config).inlineSharing erasure.rawCtx :=
    Sim.OracleRel.of_externFree (fun _ => rfl)
  obtain ⟨targetFuel, targetValue, targetEval, relatedValue⟩ := Sim.erasure_sim_with_members
    erasure.members oracles inlined.1 related (by
      simpa [Ixon.Eval.valuesInlineSharing, rawCtx] using
        (Sim.EnvRel.nil (ectx := (validatedEvalCtx constants config).inlineSharing)
          (ictx := erasure.rawCtx) (refs := (validatedMainFrame main).inlineSharing.refs)
          (muts := (validatedMainFrame main).inlineSharing.selfMuts)
          (sa := (validatedMainFrame main).inlineSharing.selfAddr)))
  rw [erasure.entryTarget] at targetEval
  exact ⟨targetFuel, targetValue, targetEval, relatedValue⟩

end Compilatrix.Pipeline.ValidatedErasure
