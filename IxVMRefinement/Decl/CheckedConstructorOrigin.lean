import IxVMRefinement.Decl.NativeConstructorConversion
import IxVMRefinement.Decl.NativeFormerChecked

/-! # Constructor correspondence from the actual complete checking stage

The original reader header is checked before field-domain normalization. Its annotation and
the actual recheck of the rebuilt type are retained together, including their common signature.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics

/-- The complete constructor stage retains the initial check and the exact normalization result. -/
theorem checkSumCtor_initial_check {md : Mode} {before env : Env md} {T : Key md}
    {levels : List LevelParam} {nP nIdx nF fuel : Nat} {sort : Level} {isProp large : Bool}
    {raw former checked : ConstantVal md} {sorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before env T levels nP nIdx sort isProp large
      raw nF former = .ok (checked, sorts)) :
    ∃ initial, checkConstantVal (fueledOps .verified fuel) env raw = .ok initial ∧
      normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked := by
  unfold checkSumCtor at run
  obtain ⟨initial, first, run⟩ := exceptBind_ok run
  obtain ⟨normalized, normalization, run⟩ := exceptBind_ok run
  obtain ⟨pair, _, run⟩ := exceptBind_ok run
  obtain ⟨binders, residual⟩ := pair
  dsimp only at run
  split at run
  · obtain ⟨constructors, _, run⟩ := exceptBind_ok run
    obtain ⟨types, _, run⟩ := exceptBind_ok run
    obtain ⟨_, _, run⟩ := exceptBind_ok run
    obtain ⟨fields, _, run⟩ := exceptBind_ok run
    split at run
    · split at run
      · split at run
        · obtain ⟨fieldSorts, _, run⟩ := exceptBind_ok run
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
          exact ⟨initial, first, normalization⟩
        · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at run
      · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at run
    · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at run
  · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at run

/-- The initially annotated constructor is genuinely stored as its raw reader header;
normalization preserves its name and levels and retains the actual final reannotation check. -/
theorem checkSumCtor_reader_origin {before env : Env .anon} (wellFormed : EnvWF env)
    {T : Key .anon} {levels : List LevelParam} {nP nIdx nF fuel : Nat} {sort : Level}
    {isProp large : Bool} {raw former checked : ConstantVal .anon} {sorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before env T levels nP nIdx sort isProp large
      raw nF former = .ok (checked, sorts)) :
    ∃ initial rebuilt,
      checkConstantVal (fueledOps .verified fuel) env raw = .ok initial ∧
      IxVM.Consistency.ValStored initial raw ∧
      checked.name = initial.name ∧ checked.levelParams = initial.levelParams ∧
      Expr.WScoped 0 rebuilt ∧ rebuilt.looseBVarsBounded 0 = true ∧
      Rules.DefEq env 0 rebuilt initial.type ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) env { raw with type := rebuilt } = .ok checked) := by
  obtain ⟨initial, first, normalized⟩ := checkSumCtor_initial_check run
  obtain ⟨rebuilt, scope, bounded, _, converted, lastCheck⟩ :=
    normCtorVal_rebuilt_conversion wellFormed first normalized
  have stored := NativeFormerRestore.initiallyStored first
  have signature : checked.name = initial.name ∧ checked.levelParams = initial.levelParams := by
    rcases lastCheck with rfl | checkedAgain
    · exact ⟨rfl, rfl⟩
    · have original := constantValCheckJ_of_run first
      have output := constantValCheckJ_of_run checkedAgain
      exact ⟨output.name_eq.trans original.name_eq.symm,
        output.levelParams_eq.trans original.levelParams_eq.symm⟩
  exact ⟨initial, rebuilt, first, stored, signature.1, signature.2, scope, bounded, converted, lastCheck⟩

end IxVM.Refinement.Decl
