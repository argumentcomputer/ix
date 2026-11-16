import IxVMRefinement.Decl.NativeConstructorFieldFrames
import IxVMRefinement.Decl.NativeFormerChecked
import IxC.Kernel.Verify.Inductives.FixInv

/-! # Reader type correspondence from the actual native recursor comparison

The recursor stage checks the declared type, infers the generated type, and compares these
two checked endpoints directly. Its actual conversion therefore supplies their graded
semantic correspondence without passing through an independent annotation relation.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term

universe u

/-- The actual native recursor check supplies a reader-shaped initial header and equality of
its type's interpretation with the generated stored type, at every level valuation. -/
theorem checkNativeRec_type_semantics {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) {fuel : Nat} {parts : NativeParts .anon}
    {former generated : ConstantVal .anon} {constructors : List (ConstantVal .anon × Nat)}
    {rules : List (Expr .anon)}
    (run : checkNativeRec (fueledOps .verified fuel) env parts former constructors = .ok (generated, rules)) :
    ∃ initial,
      checkConstantVal (fueledOps .verified fuel) env parts.cvR = .ok initial ∧
      IxVM.Consistency.ValStored initial parts.cvR ∧
      generated.name = initial.name ∧ generated.levelParams = initial.levelParams ∧
      isDefEqCore .verified env fuel 0 initial.type generated.type = .ok true ∧
      ∀ φ : LevelParam → Nat, ∃ originalReading generatedReading,
        denoteMeta model.base2.acval env φ 0 initial.type = some originalReading ∧
        denoteMeta model.base2.acval env φ 0 generated.type = some generatedReading ∧
        ∀ ρ : Nat → V, WellDenotedV V ρ originalReading ∧ WellDenotedV V ρ generatedReading ∧
          interp V ρ originalReading = interp V ρ generatedReading := by
  obtain ⟨initial, recType, sortType, sortLevel, first, _, _, _, generatedBounded,
      generatedClosed, generatedInfer, _, converted, _, generatedEq⟩ := checkNativeRec_shape run
  subst generated
  have originalStored := NativeFormerRestore.initiallyStored first
  refine ⟨initial, first, originalStored, originalStored.1.symm, originalStored.2.1.symm, converted, ?_⟩
  intro φ
  obtain ⟨originalReading, originalRead, originalGraded⟩ := checked_type_reading model first φ
  obtain ⟨originalClosed, _, _, originalBounded⟩ := checkConstantVal_typeWF first
  have originalScope : Expr.WScoped 0 initial.type := Expr.WScoped.of_not_hasFvar originalClosed
  have originalLeaves := Expr.LeavesBounded.of_not_hasFvar originalClosed
  have originalContext := CtxOk.nil (m := model.base2) (φ := φ)
    (Expr.fvarLeaves_eq_nil_of_not_hasFvar originalClosed)
  have generatedScope : Expr.WScoped 0 recType := Expr.WScoped.of_not_hasFvar generatedClosed
  have generatedLeaves := Expr.LeavesBounded.of_not_hasFvar generatedClosed
  have generatedContext := CtxOk.nil (m := model.base2) (φ := φ)
    (Expr.fvarLeaves_eq_nil_of_not_hasFvar generatedClosed)
  have judge := judgeSound_runJ rfl model fuel
  obtain ⟨generatedReading, generatedRead⟩ :=
    judge.accepted φ generatedInfer generatedScope generatedBounded generatedLeaves
  obtain ⟨_, _, generatedGraded, _, _⟩ := inferRowJ judge generatedInfer
    generatedScope generatedBounded generatedLeaves generatedContext generatedRead
  have equal := defEqRowJ judge converted originalScope originalBounded originalLeaves
    generatedScope generatedBounded generatedLeaves originalContext generatedContext originalRead generatedRead
    (fun ρ _ => originalGraded ρ) generatedGraded
  exact ⟨originalReading, generatedReading, originalRead, generatedRead,
    fun ρ => ⟨originalGraded ρ, generatedGraded ρ (Sat_nil V ρ), equal ρ (Sat_nil V ρ)⟩⟩

end IxVM.Refinement.Decl
