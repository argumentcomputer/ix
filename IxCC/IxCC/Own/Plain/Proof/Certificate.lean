import IxCC.Own.Plain.Certificate
import IxCC.Own.Plain.Proof.Owned.Program
import IxCC.Own.Plain.Proof.OwnedAccepts

set_option autoImplicit false
namespace IxCC.Own.Plain.Certificate
open Lean (Json toJson)
open IxCC.Recheck.CertJson (arr nat str nats getArr)

/-- What an accepted admission consists of: the program within the parameter total, and the
decoded map within the captured-work budget and accepted by the ownership checker. -/
theorem admit_ok {F : Fir.Program} {j : Json} {budget params : Nat} {P : Program}
    (accepted : admit F j budget params = .ok P) :
    ∃ bodies, paramTotal F ≤ params ∧ decode F j = .ok bodies ∧ capturedWork bodies ≤ budget ∧
      checkOwned F bodies = true ∧ P = { source := F, bodies } := by
  unfold admit at accepted
  cases hp : checkParamTotal params F with
  | error e => simp only [hp, bind, Except.bind] at accepted; cases accepted
  | ok u =>
    simp only [hp, bind, Except.bind] at accepted
    cases hd : decode F j with
    | error e => simp only [hd] at accepted; cases accepted
    | ok bodies =>
      simp only [hd] at accepted
      cases hb : checkBudget budget bodies with
      | error e => simp only [hb] at accepted; cases accepted
      | ok u' =>
        simp only [hb] at accepted
        split at accepted
        · next checked =>
          cases accepted
          exact ⟨bodies, checkParamTotal_ok.mp hp, rfl, checkBudget_ok.mp hb, checked, rfl⟩
        · cases accepted

theorem admit_of {F : Fir.Program} {j : Json} {budget params : Nat} {bodies : Src.NatMap Code}
    (hp : paramTotal F ≤ params) (hd : decode F j = .ok bodies) (hw : capturedWork bodies ≤ budget)
    (hc : checkOwned F bodies = true) : admit F j budget params = .ok { source := F, bodies } := by
  have hq : checkParamTotal params F = .ok () := checkParamTotal_ok.mpr hp
  have hb : checkBudget budget bodies = .ok () := checkBudget_ok.mpr hw
  simp [admit, hq, hd, hb, hc, bind, Except.bind, pure, Except.pure]

/-- **Acceptance is monotone in the budget**: a refusal for the budget is policy, not soundness;
any certificate admitted under a budget is admitted, as the same program, under a larger one. -/
theorem admit_mono {F : Fir.Program} {j : Json} {budget budget' params : Nat} {P : Program}
    (le : budget ≤ budget') (accepted : admit F j budget params = .ok P) :
    admit F j budget' params = .ok P := by
  obtain ⟨bodies, hp, hd, hw, hc, rfl⟩ := admit_ok accepted
  exact admit_of hp hd (Nat.le_trans hw le) hc

/-- **Acceptance is monotone in the parameter limit**: any certificate admitted under a limit is
admitted, as the same program, under a larger one. -/
theorem admit_params_mono {F : Fir.Program} {j : Json} {budget params params' : Nat} {P : Program}
    (le : params ≤ params') (accepted : admit F j budget params = .ok P) :
    admit F j budget params' = .ok P := by
  obtain ⟨bodies, hp, hd, hw, hc, rfl⟩ := admit_ok accepted
  exact admit_of (Nat.le_trans hp le) hd hw hc

/-- An admitted map is within the budget it was admitted under. -/
theorem admit_budget {F : Fir.Program} {j : Json} {budget params : Nat} {P : Program}
    (accepted : admit F j budget params = .ok P) : capturedWork P.bodies ≤ budget := by
  obtain ⟨bodies, _, _, hw, _, rfl⟩ := admit_ok accepted
  exact hw

/-- An admitted program is within the parameter limit it was admitted under. -/
theorem admit_paramTotal {F : Fir.Program} {j : Json} {budget params : Nat} {P : Program}
    (accepted : admit F j budget params = .ok P) : paramTotal F ≤ params := by
  obtain ⟨_, hp, _⟩ := admit_ok accepted
  exact hp

theorem admitContract_ok {F : Fir.Program} {j : Json} {budget params : Nat} {P : Program}
    (accepted : admitContract F j budget params = .ok P) :
    ∃ bodies, paramTotal F ≤ params ∧ decode F j = .ok bodies ∧ capturedWork bodies ≤ budget ∧
      checkContractOwned F bodies = true ∧ P = { source := F, bodies } := by
  unfold admitContract at accepted
  cases hp : checkParamTotal params F with
  | error e => simp only [hp, bind, Except.bind] at accepted; cases accepted
  | ok u =>
    simp only [hp, bind, Except.bind] at accepted
    cases hd : decode F j with
    | error e => simp only [hd] at accepted; cases accepted
    | ok bodies =>
      simp only [hd] at accepted
      cases hb : checkBudget budget bodies with
      | error e => simp only [hb] at accepted; cases accepted
      | ok u' =>
        simp only [hb] at accepted
        split at accepted
        · next checked =>
          cases accepted
          exact ⟨bodies, checkParamTotal_ok.mp hp, rfl, checkBudget_ok.mp hb, checked, rfl⟩
        · cases accepted

theorem admitContract_of {F : Fir.Program} {j : Json} {budget params : Nat}
    {bodies : Src.NatMap Code} (hp : paramTotal F ≤ params) (hd : decode F j = .ok bodies)
    (hw : capturedWork bodies ≤ budget) (hc : checkContractOwned F bodies = true) :
    admitContract F j budget params = .ok { source := F, bodies } := by
  have hq : checkParamTotal params F = .ok () := checkParamTotal_ok.mpr hp
  have hb : checkBudget budget bodies = .ok () := checkBudget_ok.mpr hw
  simp [admitContract, hq, hd, hb, hc, bind, Except.bind, pure, Except.pure]

/-- **Acceptance is monotone in the budget** (contract-aware admission). -/
theorem admitContract_mono {F : Fir.Program} {j : Json} {budget budget' params : Nat} {P : Program}
    (le : budget ≤ budget') (accepted : admitContract F j budget params = .ok P) :
    admitContract F j budget' params = .ok P := by
  obtain ⟨bodies, hp, hd, hw, hc, rfl⟩ := admitContract_ok accepted
  exact admitContract_of hp hd (Nat.le_trans hw le) hc

/-- **Acceptance is monotone in the parameter limit** (contract-aware admission). -/
theorem admitContract_params_mono {F : Fir.Program} {j : Json} {budget params params' : Nat}
    {P : Program} (le : params ≤ params') (accepted : admitContract F j budget params = .ok P) :
    admitContract F j budget params' = .ok P := by
  obtain ⟨bodies, hp, hd, hw, hc, rfl⟩ := admitContract_ok accepted
  exact admitContract_of (Nat.le_trans hp le) hd hw hc

/-- An admitted program is within the parameter limit it was admitted under (contract-aware
admission). -/
theorem admitContract_paramTotal {F : Fir.Program} {j : Json} {budget params : Nat} {P : Program}
    (accepted : admitContract F j budget params = .ok P) : paramTotal F ≤ params := by
  obtain ⟨_, hp, _⟩ := admitContract_ok accepted
  exact hp

/-- **Nothing admitted before heap stage 2 is refused now, within the limits.** Admission used to
accept a decoded map exactly when `checkPlainMap` did (the canonical placement, recomputed and
compared); every such map within the parameter limit and the captured-work budget is admitted
now, as the same program (`checkPlainMap_checkOwned`). -/
theorem admit_of_checkPlainMap {F : Fir.Program} {j : Json} {budget params : Nat}
    {bodies : Src.NatMap Code} (hp : paramTotal F ≤ params) (hd : decode F j = .ok bodies)
    (hw : capturedWork bodies ≤ budget) (hc : checkPlainMap F bodies = true) :
    admit F j budget params = .ok { source := F, bodies } :=
  admit_of hp hd hw (checkPlainMap_checkOwned hc)

/-- The same for contract-aware admission (`checkContractPlainMap_checkContractOwned`). -/
theorem admitContract_of_checkContractPlainMap {F : Fir.Program} {j : Json} {budget params : Nat}
    {bodies : Src.NatMap Code} (hp : paramTotal F ≤ params) (hd : decode F j = .ok bodies)
    (hw : capturedWork bodies ≤ budget) (hc : checkContractPlainMap F bodies = true) :
    admitContract F j budget params = .ok { source := F, bodies } :=
  admitContract_of hp hd hw (checkContractPlainMap_checkContractOwned hc)

/-- The only authority of decoded data is the ownership checker. -/
theorem admit_parts {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admit F j = .ok P) :
    P.source = F ∧ checkOwned F P.bodies = true := by
  obtain ⟨bodies, _, _, _, hc, rfl⟩ := admit_ok accepted
  exact ⟨rfl, hc⟩

/-- The only authority of contract-aware decoded data is `checkContractOwned`. -/
theorem admitContract_parts {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admitContract F j = .ok P) :
    P.source = F ∧ checkContractOwned F P.bodies = true := by
  obtain ⟨bodies, _, _, _, hc, rfl⟩ := admitContract_ok accepted
  exact ⟨rfl, hc⟩

theorem admit_implies_admitContract {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admit F j = .ok P) :
    admitContract F j = .ok P := by
  obtain ⟨bodies, hp, hd, hw, checked, rfl⟩ := admit_ok accepted
  exact admitContract_of hp hd hw (checkOwned_contract checked)

theorem admit_parts_contract {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admit F j = .ok P) :
    P.source = F ∧ checkContractOwned F P.bodies = true :=
  admitContract_parts (admit_implies_admitContract accepted)

theorem ofText_parts {F : Fir.Program} {text : String} {P : Program}
    (accepted : ofText F text = .ok P) :
    ∃ j, Json.parse text = .ok j ∧ admit F j = .ok P ∧
      P.source = F ∧ checkOwned F P.bodies = true := by
  unfold ofText at accepted
  cases hc : Src.Hints.checkJsonText text with
  | error e =>
    simp only [hc, bind, Except.bind] at accepted
    cases accepted
  | ok _ =>
    simp only [hc, bind, Except.bind] at accepted
    cases hp : Json.parse text with
    | error e =>
      simp only [hp] at accepted
      cases accepted
    | ok j =>
      simp only [hp] at accepted
      exact ⟨j, rfl, accepted, admit_parts accepted⟩

theorem ofTextContract_parts {F : Fir.Program} {text : String} {P : Program}
    (accepted : ofTextContract F text = .ok P) :
    ∃ j, Json.parse text = .ok j ∧ admitContract F j = .ok P ∧
      P.source = F ∧ checkContractOwned F P.bodies = true := by
  unfold ofTextContract at accepted
  cases hc : Src.Hints.checkJsonText text with
  | error e =>
    simp only [hc, bind, Except.bind] at accepted
    cases accepted
  | ok _ =>
    simp only [hc, bind, Except.bind] at accepted
    cases hp : Json.parse text with
    | error e =>
      simp only [hp] at accepted
      cases accepted
    | ok j =>
      simp only [hp] at accepted
      exact ⟨j, rfl, accepted, admitContract_parts accepted⟩

end IxCC.Own.Plain.Certificate
