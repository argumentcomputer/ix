import IxCC.Own.Plain.Certificate

set_option autoImplicit false
namespace IxCC.Own.Plain.Certificate
open Lean (Json toJson)
open IxCC.Recheck.CertJson (arr nat str nats getArr)

/-- The only authority of decoded data is the unchanged complete map checker. -/
theorem admit_parts {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admit F j = .ok P) :
    P.source = F ∧ checkPlainMap F P.bodies = true := by
  unfold admit at accepted
  cases hd : decode F j with
  | error e =>
    simp only [hd, bind, Except.bind] at accepted
    cases accepted
  | ok bodies =>
    simp only [hd, bind, Except.bind] at accepted
    split at accepted
    · next checked =>
      cases accepted
      exact ⟨rfl, checked⟩
    · cases accepted

/-- The only authority of contract-aware decoded data is `checkContractPlainMap`. -/
theorem admitContract_parts {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admitContract F j = .ok P) :
    P.source = F ∧ checkContractPlainMap F P.bodies = true := by
  unfold admitContract at accepted
  cases hd : decode F j with
  | error e =>
    simp only [hd, bind, Except.bind] at accepted
    cases accepted
  | ok bodies =>
    simp only [hd, bind, Except.bind] at accepted
    split at accepted
    · next checked =>
      cases accepted
      exact ⟨rfl, checked⟩
    · cases accepted

theorem admit_implies_admitContract {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admit F j = .ok P) :
    admitContract F j = .ok P := by
  unfold admit at accepted
  unfold admitContract
  cases hd : decode F j with
  | error e =>
    simp only [hd, bind, Except.bind] at accepted
    cases accepted
  | ok bodies =>
    simp only [hd, bind, Except.bind] at accepted ⊢
    split at accepted
    · next checked =>
      cases accepted
      obtain ⟨domain, pins, canonical⟩ := checkPlainMap_parts checked
      have bodyEq : (Program.canonical F).bodies = bodies :=
        congrArg Program.bodies canonical.symm
      have hc : checkContractPlainMap F bodies = true := by
        simp only [checkContractPlainMap, Bool.and_eq_true, bodyMapEq_iff, and_assoc]
        exact ⟨programDomain_implies_contractProgramDomain domain, pins, bodyEq⟩
      simp [hc, pure, Except.pure]
    · cases accepted

theorem admit_parts_contract {F : Fir.Program} {j : Json} {P : Program}
    (accepted : admit F j = .ok P) :
    P.source = F ∧ checkContractPlainMap F P.bodies = true :=
  admitContract_parts (admit_implies_admitContract accepted)

theorem ofText_parts {F : Fir.Program} {text : String} {P : Program}
    (accepted : ofText F text = .ok P) :
    ∃ j, Json.parse text = .ok j ∧ admit F j = .ok P ∧
      P.source = F ∧ checkPlainMap F P.bodies = true := by
  unfold ofText at accepted
  cases hp : Json.parse text with
  | error e =>
    simp only [hp, bind, Except.bind] at accepted
    cases accepted
  | ok j =>
    simp only [hp, bind, Except.bind] at accepted
    exact ⟨j, rfl, accepted, admit_parts accepted⟩

theorem ofTextContract_parts {F : Fir.Program} {text : String} {P : Program}
    (accepted : ofTextContract F text = .ok P) :
    ∃ j, Json.parse text = .ok j ∧ admitContract F j = .ok P ∧
      P.source = F ∧ checkContractPlainMap F P.bodies = true := by
  unfold ofTextContract at accepted
  cases hp : Json.parse text with
  | error e =>
    simp only [hp, bind, Except.bind] at accepted
    cases accepted
  | ok j =>
    simp only [hp, bind, Except.bind] at accepted
    exact ⟨j, rfl, accepted, admitContract_parts accepted⟩

end IxCC.Own.Plain.Certificate
