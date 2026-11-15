import IxVMRefinement.Decl.NativeNormalization
import IxC.Kernel.Verify.Inductives.StructWF
import IxC.Kernel.Verify.Denote.IndFrame

/-! # Exact origin of native constructor normalization

The original annotated telescope, the parameter frame, the field normalization runs, and
the final reannotation remain separate. Every normalized field comes with a conversion in
the original frame where the checker actually reduced it.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- The actual normalization exposes its original frame and every field conversion. -/
theorem normCtorVal_origin {md : Mode} {env : Env md} (wellFormed : EnvWF env)
    {fuel nP nF : Nat} {T : Key md} {raw initial checked : ConstantVal md}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked) :
    ∃ (parameterBinders : List (Expr md × BinderMeta)) (closedResidual : Expr md)
      (parameterVars : List (Expr md)) (openedResidual : Expr md)
      (fieldBinders : List (Expr md × BinderMeta)) (residual : Expr md)
      (fieldVars : List (Expr md)),
      initial.type.stripPis nP = some (parameterBinders, closedResidual) ∧
      openPisAtFvars nP initial.type 0 = some (parameterVars, openedResidual) ∧
      normFieldDoms (fueledOps .verified fuel) env T nP nF openedResidual =
        .ok (fieldBinders, residual) ∧
      openPisAtFvars nF openedResidual nP = some (fieldVars, residual) ∧
      parameterVars.length = nP ∧ fieldVars.length = nF ∧ fieldBinders.length = nF ∧
      (∀ j original output, fieldVars[j]? = some original → fieldBinders[j]? = some output →
        Expr.WScoped (nP + j) output.1 ∧ output.1.looseBVarsBounded 0 = true ∧
          (∀ leaf ∈ output.1.fvarLeaves, leaf ∈ original.fvarTypeD.fvarLeaves) ∧
          Rules.DefEq env (nP + j) original.fvarTypeD output.1) ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) env
          { raw with type := closeTelescope
            (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2))
              parameterVars parameterBinders ++ fieldBinders) 0 residual } = .ok checked) := by
  unfold normCtorVal at normalized
  obtain ⟨pair, stripped, rest⟩ := exceptBind_ok normalized
  obtain ⟨parameterBinders, closedResidual⟩ := pair
  have stripped := unwrapOr_ok stripped
  obtain ⟨pair, opened, rest⟩ := exceptBind_ok rest
  obtain ⟨parameterVars, openedResidual⟩ := pair
  have opened := unwrapOr_ok opened
  obtain ⟨pair, fieldsRun, rest⟩ := exceptBind_ok rest
  obtain ⟨fieldBinders, residual⟩ := pair
  obtain ⟨closed, _, _, bounded⟩ := checkConstantVal_typeWF first
  have initialScope := Expr.WScoped.of_not_hasFvar closed
  have residualScope : Expr.WScoped nP openedResidual := by
    simpa only [Nat.zero_add] using (openPisAtFvars_WScoped nP initial.type 0 opened initialScope).2
  have residualBounded := (Ix.Kernel.Verify.openPisAtFvars_bounded nP opened bounded).1
  obtain ⟨fieldVars, fieldsOpen, fieldCount, binderCount, fieldFacts⟩ :=
    normFieldDoms_sound wellFormed fieldsRun residualScope residualBounded
  refine ⟨parameterBinders, closedResidual, parameterVars, openedResidual, fieldBinders,
    residual, fieldVars, stripped, opened, fieldsRun, fieldsOpen, openPisAtFvars_length _ opened,
    fieldCount, binderCount, fieldFacts, ?_⟩
  split at rest
  · exact Or.inl (Except.ok.inj rest).symm
  · exact Or.inr rest

end IxVM.Refinement.Decl
