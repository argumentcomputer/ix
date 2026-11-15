import IxVMRefinement.Decl.ThmBodyModeled
import IxVMRefinement.Decl.ModeledRunModel
import IxC.Kernel.Semantics.Bridge.DeclIndRun

/-! # Accepted modeled declarations in the reference role order

The checking environment may differ only in the stored opaque theorem bodies. Every modeled
branch is replayed with its actual capabilities, rules, and generated projection functions.
-/

namespace IxVM.Refinement.Decl.ThmBodyView.Agrees

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- A successful modeled check produces the complete run and preserves the reference model. -/
theorem checkedModeled_modelStep {source target referenceOut : Env .anon}
    (agreement : Agrees source target) {fuel : Nat} {block : List (ConstantInfo .anon)}
    (checked : checkModeled .verified (fueledOps .verified fuel) source block = .ok referenceOut) :
    ∃ targetOut, Agrees referenceOut targetOut ∧
      DeclIndRun .verified fuel target block targetOut ∧
      ∀ (V : Type u) [SetTheory V], EnvModelT V .verified target → EnvModelT V .verified targetOut := by
  obtain ⟨targetOut, outAgreement, run⟩ := agreement.modeledRun (declIndRun_of checked)
  exact ⟨targetOut, outAgreement, run, fun _ _ inv => modeledRun_envModelT run inv⟩

end IxVM.Refinement.Decl.ThmBodyView.Agrees
