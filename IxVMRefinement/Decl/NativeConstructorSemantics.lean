import IxVMRefinement.Decl.NativeConstructorFieldFrames
import IxVMRefinement.Decl.NativeParameterReclose

/-! # The semantic output at the constructor reannotation boundary

The first successful constant check supplies a graded reading. Actual domain normalization
and parameter reclosing preserve that reading's interpretation. The separate final check
remains explicit; no equality between independently computed annotations is inferred.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term

universe u

/-- The complete pre-reannotation constructor has a graded reading equal in interpretation to
its first checked reader annotation, constructed from the actual normalization run. -/
theorem normCtorVal_rebuilt_semantics {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {fuel nP nF : Nat} {T : Key md}
    {raw initial checked : ConstantVal md}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (φ : LevelParam → Nat) :
    ∃ rebuilt initialReading rebuiltReading,
      Expr.WScoped 0 rebuilt ∧ rebuilt.looseBVarsBounded 0 = true ∧
      denoteMeta model.base2.acval env φ 0 initial.type = some initialReading ∧
      denoteMeta model.base2.acval env φ 0 rebuilt = some rebuiltReading ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ initialReading ∧ WellDenotedV V ρ rebuiltReading ∧
        interp V ρ initialReading = interp V ρ rebuiltReading) ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked) := by
  obtain ⟨parameters, _, parameterVars, openedResidual, fields, residual, _,
      stripped, opened, fieldRun, _, _, _, _, _, lastCheck⟩ :=
    normCtorVal_origin model.base2.wf first normalized
  obtain ⟨closed, _, _, bounded⟩ := checkConstantVal_typeWF first
  have frame : Ix.Kernel.Model.Rules.Frame 0 initial.type :=
    ⟨Expr.WScoped.of_not_hasFvar closed, bounded, Expr.LeavesBounded.of_not_hasFvar closed⟩
  have aligned := CtxOk.nil (m := model.base2) (φ := φ) (Expr.fvarLeaves_eq_nil_of_not_hasFvar closed)
  obtain ⟨initialReading, initialRead, initialGraded⟩ := checked_type_reading model first φ
  obtain ⟨scope, bound, _, rebuiltReading, rebuiltRead, rebuiltGraded, equal⟩ :=
    normalize_parameter_fields_semantics model stripped opened
      (by simpa only [Nat.zero_add] using fieldRun) frame aligned initialRead
      (fun ρ _ => initialGraded ρ)
  refine ⟨_, initialReading, rebuiltReading, scope, bound, initialRead, rebuiltRead, ?_, lastCheck⟩
  intro ρ
  exact ⟨initialGraded ρ, rebuiltGraded ρ (Sat_nil V ρ), equal ρ (Sat_nil V ρ)⟩

end IxVM.Refinement.Decl
