import IxVMRefinement.Decl.NativeConstructorTailAnnot
import IxVMRefinement.Decl.NativeConstructorFieldChecks
import IxVMRefinement.Decl.NativeConstructorFieldFrames
import IxC.Kernel.Model.Inductives.FormerZero

/-! # Constructor telescope metadata from the actual result-family checks

The recorded normalization and final annotation preserve the result family and its argument
count. Both actual header checks therefore infer the same result sort, which fixes every
outer parameter/field binder's datum. This does not assume metadata agreement inside domains.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics

private theorem pwsAll_of_open_bits {md : Mode} {sortLevel : Level} {name : Key md} {levels : List Level} :
    ∀ {count depth : Nat} {e body : Expr md} {fvars : List (Expr md)},
      openPisAtFvars count e depth = some (fvars, body) → body.getAppFn = .const name levels →
      (∀ φ, PiBitsOpen φ (sortLevel.eval φ = 0) count depth e) →
      pwsAll (Level.zeronessOf sortLevel) e = true
  | 0, _, e, _, _, opened, head, _ => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
    cases e with
    | forallE => cases head
    | _ => rfl
  | count + 1, depth, e, _, _, opened, head, bits => by
    cases e with
    | forallE domain body bm =>
      simp only [openPisAtFvars] at opened
      cases next : openPisAtFvars count (body.instantiate1 (.fvar depth domain)) (depth + 1) with
      | none => rw [next] at opened; cases opened
      | some pair =>
        obtain ⟨vars, output⟩ := pair
        rw [next] at opened
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
        have metadata : bm.pw = Level.zeronessOf sortLevel := by
          apply PropWhen.eq_of_holds
          intro φ
          apply Bool.eq_iff_iff.mpr
          exact pwBit_eq_zero_iff.symm.trans (((bits φ).1.trans
            (pwBit_zeronessOf φ sortLevel).symm).trans pwBit_eq_zero_iff)
        have tail := pwsAll_of_open_bits next head (fun φ => (bits φ).2)
        rw [pwsAll_instantiate1] at tail
        simpa only [pwsAll, metadata, beq_self_eq_true, Bool.true_and] using tail
    | _ => cases opened

/-- A checked telescope ending in a fully applied stored family carries that family's result datum. -/
theorem checked_telescope_family_pws {md : Mode} {env : Env md} {fuel count : Nat}
    {raw checked : ConstantVal md} {fvars : List (Expr md)} {body : Expr md}
    {name : Key md} {levels : List Level} {ci : ConstantInfo md}
    {binders : List (Expr md × BinderMeta)} {sortLevel : Level}
    (run : checkConstantVal (fueledOps .verified fuel) env raw = .ok checked)
    (opened : openPisAtFvars count checked.type 0 = some (fvars, body))
    (head : body.getAppFn = .const name levels) (found : env.find? name = some ci)
    (family : (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams levels).stripPis
      body.getAppArgs.length = some (binders, .sort sortLevel)) :
    pwsAll (Level.zeronessOf sortLevel) checked.type = true := by
  obtain ⟨_, header, equal⟩ := constantValCheckJ_of_run run
  obtain ⟨_, _, _, _, _, _, _, _, _, st, _, inferred, sorted⟩ := header
  have checkedInfer : (runJ .verified fuel).infer env 0 checked.type st := by
    simpa only [equal] using inferred
  obtain ⟨bodyType, bodySort, bodyInfer, bodySorted, _, bits⟩ :=
    piBitsJ (judgeInv_runJ rfl fuel) count opened checkedInfer sorted
  have named : (runJ .verified fuel).infer env (0 + count)
      (Expr.mkAppN (.const name levels) body.getAppArgs) bodyType := by
    rw [← head, Expr.mkAppN_getApp]
    exact bodyInfer
  have bodyTypeEq := (judgeInv_runJ rfl fuel).infer_spine_sort named found family
  subst bodyType
  have bodySortEq := (judgeInv_runJ rfl fuel).sort_sort bodySorted
  rw [bodySortEq] at bits
  exact pwsAll_of_open_bits opened head bits

/-- Both actual constructor headers have the same outer binder data, fixed by the stored family's
result sort. Domain metadata remains a separate correspondence obligation. -/
theorem checkSumCtor_outer_metadata {before env : Env .anon} {T : Key .anon}
    {levels : List LevelParam} {nP nIdx nF fuel : Nat} {sortLevel : Level}
    {isProp large : Bool} {raw former checked : ConstantVal .anon} {sorts : List Level}
    {familyCI : ConstantInfo .anon} {familyBinders : List (Expr .anon × BinderMeta)}
    (run : checkSumCtor (fueledOps .verified fuel) before env T levels nP nIdx sortLevel isProp large
      raw nF former = .ok (checked, sorts))
    (found : env.find? T = some familyCI)
    (family : (familyCI.toConstantVal.type.instantiateLevelParams familyCI.toConstantVal.levelParams
      (levels.map .param)).stripPis (nP + nIdx) = some (familyBinders, .sort sortLevel)) :
    ∃ initial, checkConstantVal (fueledOps .verified fuel) env raw = .ok initial ∧
      normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked ∧
      pwsAll (Level.zeronessOf sortLevel) initial.type = true ∧
      pwsAll (Level.zeronessOf sortLevel) checked.type = true := by
  obtain ⟨initial, first, normalized⟩ := checkSumCtor_initial_check run
  obtain ⟨rebuilt, rebuild, _⟩ := normCtorVal_rebuild_trace normalized
  obtain ⟨_, _, originalParams, _, _, originalResidual, _, originalOpen, fieldRun, _⟩ := rebuild
  obtain ⟨originalFields, originalFieldsOpen, _, _⟩ := normFieldDoms_calls fieldRun
  have originalWhole := openPisAtFvars_add nP originalOpen (by rw [Nat.zero_add]; exact originalFieldsOpen)
  obtain ⟨⟨_, lastCheck⟩, _, finalParams, _, _, _, finalFields, indices,
      finalOpen, _, _, finalFieldsOpen, indexCount, _, _, _⟩ := checkSumCtor_shape run
  have finalWhole := openPisAtFvars_add nP finalOpen (by rw [Nat.zero_add]; exact finalFieldsOpen)
  have parameterCount := Ix.Kernel.Verify.openPisAtFvars_length _ finalOpen
  have finalShape : applicationShape (Expr.mkAppN (.const T (levels.map .param)) (finalParams ++ indices)) =
      (some (T, levels.map .param), nP + nIdx) := by
    simp only [applicationShape_mkAppN, applicationShape, List.length_append, parameterCount, indexCount, Nat.zero_add]
  have tails := normCtorVal_result_shape first normalized
  rw [telescopeTailShape_of_open finalWhole, telescopeTailShape_of_open originalWhole] at tails
  have originalShape := (Option.some.inj tails).symm.trans finalShape
  obtain ⟨originalHead, originalArity⟩ := applicationShape_const_inv originalShape
  obtain ⟨finalHead, finalArity⟩ := applicationShape_const_inv finalShape
  refine ⟨initial, first, normalized, ?_, ?_⟩
  · apply checked_telescope_family_pws first originalWhole originalHead found
    rw [originalArity]
    exact family
  · apply checked_telescope_family_pws lastCheck finalWhole finalHead found
    rw [finalArity]
    exact family

end IxVM.Refinement.Decl
