import IxVMRefinement.Decl.NativeParameterReclose
import IxVMRefinement.Decl.NativeConstructorOrigin

/-! # The actual two-check boundary of constructor normalization

The rebuilt type converts to the first checked reader annotation. The final constructor
is either that first result or the result of the separate recorded check of the rebuilt type.
No equality between independent annotations is inferred from the conversion.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- The exact recorded rebuilt expression converts to the initially checked header. -/
theorem ConstructorRebuildRun.conversion {md : Mode} {env : Env md} (wellFormed : EnvWF env)
    {fuel nP nF : Nat} {T : Key md} {raw initial : ConstantVal md} {rebuilt : Expr md}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (rebuild : ConstructorRebuildRun env fuel T nP nF initial.type rebuilt) :
    Expr.WScoped 0 rebuilt ∧ rebuilt.looseBVarsBounded 0 = true ∧
      (∀ leaf ∈ rebuilt.fvarLeaves, leaf ∈ initial.type.fvarLeaves) ∧
      Rules.DefEq env 0 rebuilt initial.type := by
  obtain ⟨parameters, closedResidual, parameterVars, openedResidual, fields, residual,
      stripped, opened, fieldRun, rfl⟩ := rebuild
  obtain ⟨closed, _, _, bounded⟩ := checkConstantVal_typeWF first
  have scope : Expr.WScoped 0 initial.type := Expr.WScoped.of_not_hasFvar closed
  have openedScope : Expr.WScoped nP openedResidual := by
    simpa only [Nat.zero_add] using (openPisAtFvars_WScoped nP initial.type 0 opened scope).2
  have openedBounded := (Ix.Kernel.Verify.openPisAtFvars_bounded nP opened bounded).1
  obtain ⟨_, fieldScope, fieldBounded, fieldLeaves, fieldEq⟩ :=
    normFieldDoms_reclose wellFormed fieldRun openedScope openedBounded
  have prefixFacts := reclose_parameter_prefix stripped opened scope bounded
    (by simpa only [Nat.zero_add] using fieldScope) fieldBounded fieldLeaves
    (by simpa only [Nat.zero_add] using fieldEq)
  let pbs := List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) parameterVars parameters
  have parameterCount := Ix.Kernel.Verify.openPisAtFvars_length _ opened
  have binderCount : parameters.length = nP := Expr.stripPis_length _ stripped
  have pbsCount : pbs.length = nP := by
    simp only [pbs, List.length_zipWith, parameterCount, binderCount, Nat.min_self]
  have reclosed : closeTelescope (pbs ++ fields) 0 residual =
      closeTelescope pbs 0 (closeTelescope fields nP residual) := by
    rw [closeTelescope_append, pbsCount, Nat.zero_add]
  change Expr.WScoped 0 (closeTelescope pbs 0 (closeTelescope fields nP residual)) ∧ _ at prefixFacts
  rw [← reclosed] at prefixFacts
  exact prefixFacts

/-- Both actual checks and the whole pre-reannotation conversion are recovered from normalization. -/
theorem normCtorVal_rebuilt_conversion {md : Mode} {env : Env md} (wellFormed : EnvWF env)
    {fuel nP nF : Nat} {T : Key md} {raw initial checked : ConstantVal md}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked) :
    ∃ rebuilt,
      Expr.WScoped 0 rebuilt ∧ rebuilt.looseBVarsBounded 0 = true ∧
      (∀ leaf ∈ rebuilt.fvarLeaves, leaf ∈ initial.type.fvarLeaves) ∧
      Rules.DefEq env 0 rebuilt initial.type ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked) := by
  obtain ⟨rebuilt, rebuild, lastCheck⟩ := normCtorVal_rebuild_trace normalized
  obtain ⟨scope, bounded, leaves, converted⟩ := rebuild.conversion wellFormed first
  exact ⟨rebuilt, scope, bounded, leaves, converted, lastCheck⟩

end IxVM.Refinement.Decl
