import Ix.Ixon.WireCheck

namespace Ixon.Verify.WireCheck

open _root_.Ixon _root_.Ixon.WireCheck

theorem checkUniv_complete (u : Univ) (wf : u.wireWF) :
    ∃ result, checkUniv u = some result := by
  induction u with
  | zero => exact ⟨_, rfl⟩
  | var _ => exact ⟨_, rfl⟩
  | succ inner ih =>
    obtain ⟨child, read⟩ := ih wf.2
    have fits : child.count + 1 < UInt64.size := by
      simpa [child.count_eq, Univ.succCountNat, Nat.add_comm] using wf.1
    simp [checkUniv, read, fits]
  | max left right ihLeft ihRight =>
    obtain ⟨left, readLeft⟩ := ihLeft wf.1
    obtain ⟨right, readRight⟩ := ihRight wf.2
    simp [checkUniv, readLeft, readRight]
  | imax left right ihLeft ihRight =>
    obtain ⟨left, readLeft⟩ := ihLeft wf.1
    obtain ⟨right, readRight⟩ := ihRight wf.2
    simp [checkUniv, readLeft, readRight]

theorem checkExpr_complete (e : Expr) (wf : e.wireWF) :
    ∃ result, checkExpr e = some result := by
  induction e with
  | sort _ => exact ⟨_, rfl⟩
  | var _ => exact ⟨_, rfl⟩
  | str _ => exact ⟨_, rfl⟩
  | nat _ => exact ⟨_, rfl⟩
  | share _ => exact ⟨_, rfl⟩
  | ref idx idxs => simp [checkExpr, show idxs.size < UInt64.size from wf]
  | recur idx idxs => simp [checkExpr, show idxs.size < UInt64.size from wf]
  | prj typeIdx field value ih =>
    obtain ⟨value, read⟩ := ih wf
    simp [checkExpr, read]
  | app fn arg ihFn ihArg =>
    obtain ⟨fn, readFn⟩ := ihFn wf.1
    obtain ⟨arg, readArg⟩ := ihArg wf.2.1
    have fits : fn.apps + 1 < UInt64.size := by simpa [fn.apps_eq] using wf.2.2
    simp [checkExpr, readFn, readArg, fits]
  | lam uses ty body ihTy ihBody =>
    obtain ⟨ty, readTy⟩ := ihTy wf.1
    obtain ⟨body, readBody⟩ := ihBody wf.2.1
    have fits : body.lams + 1 < UInt64.size := by simpa [body.lams_eq] using wf.2.2
    simp [checkExpr, readTy, readBody, fits]
  | all uses owned ty body ihTy ihBody =>
    obtain ⟨ty, readTy⟩ := ihTy wf.1
    obtain ⟨body, readBody⟩ := ihBody wf.2.1
    have fits : body.alls + 1 < UInt64.size := by simpa [body.alls_eq] using wf.2.2
    simp [checkExpr, readTy, readBody, fits]
  | letE nonDep ty value body ihTy ihValue ihBody =>
    obtain ⟨ty, readTy⟩ := ihTy wf.1
    obtain ⟨value, readValue⟩ := ihValue wf.2.1
    obtain ⟨body, readBody⟩ := ihBody wf.2.2
    simp [checkExpr, readTy, readValue, readBody]

@[simp] theorem validUniv_iff (u : Univ) : validUniv u = true ↔ u.wireWF := by
  constructor
  · intro h
    obtain ⟨result, _⟩ := Option.isSome_iff_exists.mp h
    exact result.valid
  · intro wf
    exact Option.isSome_iff_exists.mpr (checkUniv_complete u wf)

@[simp] theorem validExpr_iff (e : Expr) : validExpr e = true ↔ e.wireWF := by
  constructor
  · intro h
    obtain ⟨result, _⟩ := Option.isSome_iff_exists.mp h
    exact result.valid
  · intro wf
    exact Option.isSome_iff_exists.mpr (checkExpr_complete e wf)

@[simp] theorem validDefinition_iff (d : Definition) : validDefinition d = true ↔ d.wireWF := by
  simp [validDefinition, Definition.wireWF]

@[simp] theorem validRecursor_iff (r : Recursor) : validRecursor r = true ↔ r.wireWF := by
  simp [validRecursor, Recursor.wireWF, RecursorRule.wireWF, validArray,
    -Array.all_eq_true, Array.all_eq_true']

@[simp] theorem validInductive_iff (i : Inductive) : validInductive i = true ↔ i.wireWF := by
  simp [validInductive, Inductive.wireWF, Constructor.wireWF, validArray,
    -Array.all_eq_true, Array.all_eq_true']

@[simp] theorem validMutConst_iff (m : MutConst) : validMutConst m = true ↔ m.wireWF := by
  cases m <;> simp [validMutConst, MutConst.wireWF]

@[simp] theorem validInfo_iff (info : ConstantInfo) : validInfo info = true ↔ info.wireWF := by
  cases info <;> simp [validInfo, ConstantInfo.wireWF, Axiom.wireWF, Quotient.wireWF,
    validArray, -Array.all_eq_true, Array.all_eq_true']

/-- Soundness and completeness for every production constant variant and
every structural condition in the retained wire invariant. -/
theorem validConstant_iff (constant : Constant) :
    validConstant constant = true ↔ constant.wireWF := by
  simp [validConstant, Constant.wireWF, validArray, -Array.all_eq_true,
    Array.all_eq_true', and_assoc]

end Ixon.Verify.WireCheck
