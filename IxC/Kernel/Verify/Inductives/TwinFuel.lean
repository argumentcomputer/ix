module

public import IxC.Kernel.Inductives.TwinInstall
public import IxC.Kernel.Verify.BridgeDecl

public section

/-! # Fuel equations for the executable twin phases -/

namespace Ix.Kernel.NativeTwin

variable {mode : CheckMode}

theorem checkHeader_datF (env : Env md) (ci : ConstantInfo md) (fuel : Nat) :
    (checkHeader (fueledOpsM mode) env ci).val fuel =
      checkHeader (fueledOps mode fuel) env ci := by
  cases ci with
  | recInfo cv mI rP rules =>
    unfold checkHeader
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext annotated
    datF_tac
  | _ => rfl

theorem checkHeaders_datF (env : Env md) (fuel : Nat) : ∀ block : List (ConstantInfo md),
    (checkHeaders (fueledOpsM mode) env block).val fuel =
      checkHeaders (fueledOps mode fuel) env block
  | [] => rfl
  | ci :: block => by
    unfold checkHeaders
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkHeader_datF,
      checkHeaders_datF env fuel block]

theorem prepare_datF (env : Env md) (block : List (ConstantInfo md)) (fuel : Nat) :
    (prepare (fueledOpsM mode) env block).val fuel =
      prepare (fueledOps mode fuel) env block := by
  unfold prepare
  repeat' first
  | rw [checkHeaders_datF]
  | datF_step_alt

theorem checkRule_datF (env envSelf : Env md) (part : Part md) (raw canonical : RecRule md)
    (fuel : Nat) :
    (checkRule (fueledOpsM mode) env envSelf part raw canonical).val fuel =
      checkRule (fueledOps mode fuel) env envSelf part raw canonical := by
  unfold checkRule
  datF_tac

theorem checkRules_datF (env envSelf : Env md) (part : Part md) (fuel : Nat) :
    ∀ raws canonicals,
      (checkRules (fueledOpsM mode) env envSelf part raws canonicals).val fuel =
        checkRules (fueledOps mode fuel) env envSelf part raws canonicals
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | raw :: raws, canonical :: canonicals => by
    unfold checkRules
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkRule_datF,
      checkRules_datF env envSelf part fuel raws canonicals]

theorem checkPartsRules_datF (env envSelf : Env md) (fuel : Nat) :
    ∀ parts : List (Part md),
      (checkPartsRules (fueledOpsM mode) env envSelf parts).val fuel =
        checkPartsRules (fueledOps mode fuel) env envSelf parts
  | [] => rfl
  | part :: parts => by
    unfold checkPartsRules
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkRules_datF,
      checkPartsRules_datF env envSelf fuel parts]

theorem finish_datF (env : Env md) (parts : List (Part md)) (fuel : Nat) :
    (finish (m := FueledM md) env parts).val fuel = finish (m := CheckM md) env parts := by
  unfold finish
  datF_tac

theorem check_datF (env : Env md) (block : List (ConstantInfo md)) (fuel : Nat) :
    (check (fueledOpsM mode) env block).val fuel = check (fueledOps mode fuel) env block := by
  unfold check
  simp only [FueledM.atF_bind, prepare_datF, checkPartsRules_datF, finish_datF]

theorem check_mono {env output : Env md} {block : List (ConstantInfo md)} {fuel larger : Nat}
    (hle : fuel ≤ larger) (h : check (fueledOps mode fuel) env block = .ok output) :
    check (fueledOps mode larger) env block = .ok output := by
  rw [← check_datF] at h ⊢
  exact (check (fueledOpsM mode) env block).property hle h

end Ix.Kernel.NativeTwin
