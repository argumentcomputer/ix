import IxC.Kernel.Model.DeclInd
import IxC.Kernel.Model.FoldJ

/-! # The full modeled run preserves theorem-value model facts

The actual run includes the single-constructor capabilities and projection-function phase.
Its model extension retains the readings of previously stored annotated theorem values.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- Both actual modeled branches preserve the model and theorem-value invariant. -/
theorem modeledRun_envModelT {md : Mode} {V : Type u} [SetTheory V]
    {fuel : Nat} {env env₂ : Env md} {block : List (ConstantInfo md)}
    (run : DeclIndRun .verified fuel env block env₂)
    (inv : EnvModelT V .verified env) : EnvModelT V .verified env₂ := by
  obtain ⟨⟨model, thms⟩, eta⟩ := inv
  obtain ⟨model₂, extension⟩ := Ix.Kernel.Model.declIndExt rfl model eta run
  exact ⟨⟨model₂, thms.of_ext extension⟩, declIndEtaClosedRun eta run⟩

end IxVM.Refinement.Decl
