import IxVMRefinement.Decl.DependentBetaShape
import IxVMRefinement.Decl.DomainTransport

/-! # Producing the final reference for a checked dependent-beta field

The original reference's scope supplies its earlier position. The actual field normalization
retains that reference; the same recorded rebuilt expression closes it to a bound variable.
Annotation and reopening then produce the corresponding final-frame entry. This removes a
separate final-use shape premise from the local checked identity-beta transport.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

private theorem IdentityRef.reference_scoped {domainSort : Level} {reference e : Expr .anon} {depth : Nat}
    (origin : IdentityRef domainSort reference e) (bounded : Expr.WScoped depth e) : Expr.WScoped depth reference := by
  cases origin with
  | reference => exact bounded
  | beta => exact (show _ ∧ _ from bounded).2

/-- The final variable/redex shape is derived from the exact rebuild and final annotation.
Only the selected original use is identified by the caller. -/
theorem constructor_rebuild_identity_domain {env : Env .anon} {fuel nP nF slot target : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {rebuilt : Expr .anon}
    {originalVars finalVars : List (Expr .anon)} {originalResidual finalResidual : Expr .anon}
    {originalArgument finalArgument originalUse finalUse : Expr .anon} {domainSort : Level}
    (frames : CheckedFramePair env fuel (nP + nF) originalVars finalVars)
    (rebuild : ConstructorRebuildRun env fuel T nP nF initial.type rebuilt)
    (lastBranch : checked = initial ∨
      checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalArgumentAt : originalVars[target]? = some originalArgument)
    (finalArgumentAt : finalVars[target]? = some finalArgument)
    (originalUseAt : originalVars[nP + slot]? = some originalUse)
    (finalUseAt : finalVars[nP + slot]? = some finalUse)
    (origin : IdentityRef domainSort originalArgument originalUse.fvarTypeD) :
    IdentityRef domainSort finalArgument finalUse.fvarTypeD := by
  have argumentIndex := frames.original.indexed target originalArgument originalArgumentAt
  have referenceScope := origin.reference_scoped
    (frames.original.domainScope (nP + slot) originalUse originalUseAt).1
  rw [argumentIndex] at referenceScope
  have earlier : target < nP + slot := (show _ ∧ _ from referenceScope).1
  rcases lastBranch with same | checkedAgain
  · rw [same] at finalOpen
    obtain ⟨sameVars, _⟩ := Prod.mk.inj (Option.some.inj (originalOpen.symm.trans finalOpen))
    rw [← sameVars] at finalArgumentAt finalUseAt
    have sameArgument := Option.some.inj (originalArgumentAt.symm.trans finalArgumentAt)
    have sameUse := Option.some.inj (originalUseAt.symm.trans finalUseAt)
    rw [← sameArgument, ← sameUse]
    exact origin
  · obtain ⟨parameters, closedResidual, parameterVars, openedResidual, fields, residual,
      stripped, parametersOpen, fieldRun, rebuiltEq⟩ := rebuild
    obtain ⟨fieldVars, fieldsOpen, fieldCount, calls⟩ := normFieldDoms_calls fieldRun
    have wholeOpen : openPisAtFvars (nP + nF) initial.type 0 = some (parameterVars ++ fieldVars, residual) :=
      openPisAtFvars_add nP parametersOpen (by rw [Nat.zero_add]; exact fieldsOpen)
    obtain ⟨sameVars, _⟩ := Prod.mk.inj (Option.some.inj (originalOpen.symm.trans wholeOpen))
    have parameterCount := Ix.Kernel.Verify.openPisAtFvars_length _ parametersOpen
    have originalFieldAt : fieldVars[slot]? = some originalUse := by
      rw [sameVars, List.getElem?_append_right (by omega), parameterCount, Nat.add_sub_cancel_left] at originalUseAt
      exact originalUseAt
    have inside : slot < fields.length := by
      have bound := (List.getElem?_eq_some_iff.mp originalFieldAt).1
      rw [normFieldDoms_count fieldRun]
      omega
    have outputAt : fields[slot]? = some fields[slot] := List.getElem?_eq_getElem inside
    have variableOrigin : IdentityRef domainSort (.fvar target originalArgument.fvarTypeD) originalUse.fvarTypeD := by
      rw [← argumentIndex]
      exact origin
    have outputOrigin := variableOrigin.normalized (calls slot originalUse fields[slot] originalFieldAt outputAt)
    let parameterBinders := List.zipWith
      (fun (x : Expr .anon) (b : Expr .anon × BinderMeta) => (x.fvarTypeD, b.2)) parameterVars parameters
    have parameterBinderCount : parameterBinders.length = nP := by
      simp only [parameterBinders, List.length_zipWith, parameterCount, Expr.stripPis_length _ stripped, Nat.min_self]
    have outputWholeAt : (parameterBinders ++ fields)[nP + slot]? = some fields[slot] := by
      rw [List.getElem?_append_right (by omega), parameterBinderCount, Nat.add_sub_cancel_left]
      exact outputAt
    have annotation := (NativeFormerRestore.initiallyStored checkedAgain).2.2
    rw [rebuiltEq] at annotation
    obtain ⟨reference, referenceAt, finalOrigin⟩ := reclosed_identity_domain outputWholeAt earlier outputOrigin
      annotation finalOpen finalUseAt
    have sameReference := Option.some.inj (referenceAt.symm.trans finalArgumentAt)
    rw [sameReference] at finalOrigin
    exact finalOrigin

/-- The local dependent-beta case derives its final use shape, both sort checks, and the
argument comparison from the recorded constructor frames and exact rebuild. -/
theorem CheckedFramePair.identity_normalized_sorts {env : Env .anon} {fuel nP nF kindSlot useSlot : Nat}
    {T : Key .anon} {raw initial checked : ConstantVal .anon} {rebuilt : Expr .anon}
    {originalVars finalVars : List (Expr .anon)} {originalResidual finalResidual : Expr .anon}
    {originalArgument finalArgument originalUse finalUse : Expr .anon} {kind domainSort : Level} {metadata : BinderMeta}
    (frames : CheckedFramePair env fuel (nP + nF) originalVars finalVars)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (rebuild : ConstructorRebuildRun env fuel T nP nF initial.type rebuilt)
    (lastBranch : checked = initial ∨
      checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalArgumentAt : originalVars[nP + kindSlot]? = some originalArgument)
    (finalArgumentAt : finalVars[nP + kindSlot]? = some finalArgument)
    (originalUseAt : originalVars[nP + useSlot]? = some originalUse)
    (finalUseAt : finalVars[nP + useSlot]? = some finalUse)
    (kindOrigin : SortFunction kind 0 originalArgument.fvarTypeD)
    (oldShape : originalUse.fvarTypeD = .app (.lam (.sort domainSort) (.bvar 0) metadata) originalArgument) :
    ∃ inputType inputSort outputType outputSort,
      inferTypeCore .verified env fuel (nP + useSlot) originalUse.fvarTypeD = .ok inputType ∧
      ensureSortCore .verified env fuel (nP + useSlot) inputType = .ok inputSort ∧
      inferTypeCore .verified env fuel (nP + useSlot) finalUse.fvarTypeD = .ok outputType ∧
      ensureSortCore .verified env fuel (nP + useSlot) outputType = .ok outputSort ∧
      IdentityRef domainSort finalArgument finalUse.fvarTypeD ∧
      Rules.DefEq env (nP + useSlot) originalArgument.fvarTypeD (.sort domainSort) ∧
      Level.zeronessOf inputSort = Level.zeronessOf outputSort := by
  have pair := sortKindPair_of_rebuild frames normalized originalOpen finalOpen originalArgumentAt finalArgumentAt kindOrigin
  have afterShape := constructor_rebuild_identity_domain frames rebuild lastBranch originalOpen finalOpen
    originalArgumentAt finalArgumentAt originalUseAt finalUseAt (by rw [oldShape]; exact IdentityRef.beta)
  obtain ⟨inputType, inputSort, inputTyped, inputSorted⟩ :=
    frames.original.domainChecks (nP + useSlot) originalUse originalUseAt
  obtain ⟨outputType, outputSort, outputTyped, outputSorted⟩ :=
    frames.final.domainChecks (nP + useSlot) finalUse finalUseAt
  have beforeTyped := Rules.inferTypeCore_bridge inputTyped
  rw [oldShape] at beforeTyped
  have equal := pair.identity_result beforeTyped (Rules.whnf_bridge (ensureSortCore_inv inputSorted))
    afterShape (Rules.inferTypeCore_bridge outputTyped) (Rules.whnf_bridge (ensureSortCore_inv outputSorted))
  obtain ⟨_, argumentType, argumentTyped, compared⟩ := infer_identity_application beforeTyped
  have typeEq : argumentType = originalArgument.fvarTypeD := by
    rw [pair.originalIndex] at argumentTyped
    exact Rules.Infer.fvar_inv argumentTyped
  rw [typeEq] at compared
  exact ⟨inputType, inputSort, outputType, outputSort, inputTyped, inputSorted,
    outputTyped, outputSorted, afterShape, compared, equal⟩

end IxVM.Refinement.Decl
