import Compilatrix.Own.Plain.Certificate

set_option autoImplicit false
namespace Compilatrix.Own.Plain.Certificate
open Lean (Json toJson)
open Compilatrix.Recheck.CertJson (arr nat str nats getArr)

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

end Compilatrix.Own.Plain.Certificate
