import IxVMRefinement.Decl.CheckedConstructorOrigin
import IxC.Kernel.Model.Inductives.FixTeleBound

/-! # The two actual constructor domain checks

The first check retains the reader-shaped telescope; the final check runs after domain
normalization and reannotation. Both sets of domain inferences are extracted at their own
actual free-variable annotations. No equality between those frames is assumed.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics

/-- A checked header supplies every opened domain's own inference and sort evidence. -/
theorem checked_type_domain_checksJ {md : Mode} {J : Judgements md}
    (inversions : JudgeInv J) {env : Env md} {count : Nat}
    {raw checked : ConstantVal md} {fvars : List (Expr md)} {residual : Expr md}
    (run : ConstantValCheckJ J env raw checked)
    (opened : openPisAtFvars count checked.type 0 = some (fvars, residual)) :
    ∀ j domain, fvars[j]? = some domain → ∃ type sortLevel,
      J.infer env j domain.fvarTypeD type ∧ J.sort env j type sortLevel := by
  obtain ⟨_, header, equal⟩ := run
  obtain ⟨_, _, _, _, _, _, _, _, _, st, s, inferred, sorted⟩ := header
  have checkedInfer : J.infer env 0 checked.type st := by
    simpa only [equal] using inferred
  intro j domain atIndex
  obtain ⟨type, sortLevel, checkedDomain, sortedDomain, _⟩ :=
    piDomsJ inversions count opened checkedInfer sorted j domain atIndex
  exact ⟨type, sortLevel, by simpa only [Nat.zero_add] using checkedDomain,
    by simpa only [Nat.zero_add] using sortedDomain⟩

/-- Every domain in the checked telescope has an actual inference and sort check at its own depth. -/
theorem checked_type_domain_checks {md : Mode} {env : Env md} {fuel count : Nat}
    {raw checked : ConstantVal md} {fvars : List (Expr md)} {residual : Expr md}
    (run : checkConstantVal (fueledOps .verified fuel) env raw = .ok checked)
    (opened : openPisAtFvars count checked.type 0 = some (fvars, residual)) :
    ∀ j domain, fvars[j]? = some domain → ∃ type sortLevel,
      inferTypeCore .verified env fuel j domain.fvarTypeD = .ok type ∧
      ensureSortCore .verified env fuel j type = .ok sortLevel :=
  checked_type_domain_checksJ (judgeInv_runJ rfl fuel) (constantValCheckJ_of_run run) opened

/-- The exact initial check and rebuilt expression are retained with both opener lists and
their domain checks. The final check is the actual branch at that same rebuilt expression. -/
theorem checkSumCtor_rebuild_domain_checks {md : Mode} {before env : Env md}
    (wellFormed : EnvWF env) {T : Key md} {levels : List LevelParam} {nP nIdx nF fuel : Nat}
    {sortLevel : Level} {isProp large : Bool} {raw former checked : ConstantVal md} {sorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before env T levels nP nIdx sortLevel isProp large
      raw nF former = .ok (checked, sorts)) :
    ∃ initial rebuilt originalVars originalResidual finalVars finalResidual,
      checkConstantVal (fueledOps .verified fuel) env raw = .ok initial ∧
      normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked ∧
      ConstructorRebuildRun env fuel T nP nF initial.type rebuilt ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked) ∧
      openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual) ∧
      openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual) ∧
      originalVars.length = nP + nF ∧ finalVars.length = nP + nF ∧
      ∀ j original final, originalVars[j]? = some original → finalVars[j]? = some final →
        ∃ originalType originalSort finalType finalSort,
          inferTypeCore .verified env fuel j original.fvarTypeD = .ok originalType ∧
          ensureSortCore .verified env fuel j originalType = .ok originalSort ∧
          inferTypeCore .verified env fuel j final.fvarTypeD = .ok finalType ∧
          ensureSortCore .verified env fuel j finalType = .ok finalSort := by
  obtain ⟨initial, first, normalized⟩ := checkSumCtor_initial_check run
  obtain ⟨rebuilt, rebuild, lastBranch⟩ := normCtorVal_rebuild_trace normalized
  obtain ⟨_, _, originalParams, _, _, originalResidual, originalFields,
      _, originalOpen, _, originalFieldsOpen, _, _, _, _, _⟩ :=
    normCtorVal_origin wellFormed first normalized
  have originalWhole : openPisAtFvars (nP + nF) initial.type 0 =
      some (originalParams ++ originalFields, originalResidual) :=
    openPisAtFvars_add nP originalOpen (by rw [Nat.zero_add]; exact originalFieldsOpen)
  obtain ⟨⟨_, lastCheck⟩, _, finalParams, _, _, _, finalFields, indices,
      finalOpen, _, _, finalFieldsOpen, _, _, _, _⟩ := checkSumCtor_shape run
  have finalWhole : openPisAtFvars (nP + nF) checked.type 0 =
      some (finalParams ++ finalFields, Expr.mkAppN (.const T (levels.map .param)) (finalParams ++ indices)) :=
    openPisAtFvars_add nP finalOpen (by rw [Nat.zero_add]; exact finalFieldsOpen)
  refine ⟨initial, rebuilt, originalParams ++ originalFields, originalResidual,
    finalParams ++ finalFields, _, first, normalized, rebuild, lastBranch, originalWhole, finalWhole,
    Ix.Kernel.Verify.openPisAtFvars_length _ originalWhole,
    Ix.Kernel.Verify.openPisAtFvars_length _ finalWhole, ?_⟩
  intro j original final originalAt finalAt
  obtain ⟨originalType, originalSort, originalInfer, originalSorted⟩ :=
    checked_type_domain_checks first originalWhole j original originalAt
  obtain ⟨finalType, finalSort, finalInfer, finalSorted⟩ :=
    checked_type_domain_checks lastCheck finalWhole j final finalAt
  exact ⟨originalType, originalSort, finalType, finalSort,
    originalInfer, originalSorted, finalInfer, finalSorted⟩

/-- A successful constructor check constructs both complete opener lists and every paired domain
check. The first list is before normalization; the second includes the final reannotation. -/
theorem checkSumCtor_paired_domain_checks {md : Mode} {before env : Env md}
    (wellFormed : EnvWF env) {T : Key md} {levels : List LevelParam} {nP nIdx nF fuel : Nat}
    {sortLevel : Level} {isProp large : Bool} {raw former checked : ConstantVal md} {sorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before env T levels nP nIdx sortLevel isProp large
      raw nF former = .ok (checked, sorts)) :
    ∃ initial originalVars originalResidual finalVars finalResidual,
      checkConstantVal (fueledOps .verified fuel) env raw = .ok initial ∧
      openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual) ∧
      openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual) ∧
      originalVars.length = nP + nF ∧ finalVars.length = nP + nF ∧
      ∀ j original final, originalVars[j]? = some original → finalVars[j]? = some final →
        ∃ originalType originalSort finalType finalSort,
          inferTypeCore .verified env fuel j original.fvarTypeD = .ok originalType ∧
          ensureSortCore .verified env fuel j originalType = .ok originalSort ∧
          inferTypeCore .verified env fuel j final.fvarTypeD = .ok finalType ∧
          ensureSortCore .verified env fuel j finalType = .ok finalSort := by
  obtain ⟨initial, _, originalVars, originalResidual, finalVars, finalResidual,
    first, _, _, _, originalOpen, finalOpen, originalCount, finalCount, domains⟩ :=
    checkSumCtor_rebuild_domain_checks wellFormed run
  exact ⟨initial, originalVars, originalResidual, finalVars, finalResidual,
    first, originalOpen, finalOpen, originalCount, finalCount, domains⟩

end IxVM.Refinement.Decl
