import IxCC.Own.Plain.Proof.Simulation
import IxCC.Own.Plain.Check

/-! Close the source-level contract with an executable Boolean-pin check.
Only successfully resolved primitive Boolean constructors need be fieldless;
unresolved pins already produce source stuck. Heap invariants are constructed
from the actual input denotations and exact incoming ownership counts. -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc

theorem canonical_call_refines {F : Fir.Program} (domain : programDomain F = true)
    (pins : checkBoolPins F = true) (k : Nat) {f : Fir.FunId} (hf : f < F.size)
    {H : Heap} {external : Nat → Nat} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws) (evalCall (Program.canonical F) k f vs H) :=
  call_of_smaller_clocks domain
    (fun j _ => canonical_refines domain (checkBoolPins_sound pins) j) hf hd hb

theorem checked_body_refines {F : Fir.Program} {f : Fir.FunId} {proposal : Code}
    (checked : checkPlainFunction F f proposal = true)
    {fd : Fir.Fun} (lookup : F.fun? f = some fd) (k : Nat)
    {H : Heap} {external : Nat → Nat} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hb : Balance H external vs)
    (arity : vs.length = fd.params.length) :
    ResultRel H external
      (Fir.eval F k (Fir.bindAll .leaf (fd.params.map (·.1)) ws) [] fd.body)
      (eval (Program.canonical F) k (Own.bindAll .leaf (fd.params.map (·.1)) vs) [] H proposal) := by
  have hs : checkBoolPins F = true ∧ checkFunction F f proposal = true := by
    simpa only [checkPlainFunction, Bool.and_eq_true] using checked
  obtain ⟨fd', hf, hfd, _, hbody⟩ := checkFunction_parts hs.2
  have eqfd : fd' = fd := Option.some.inj (hfd.symm.trans lookup)
  subst fd'
  obtain ⟨fresh, scope, code⟩ := (checkBody_iff ..).mp hbody
  rw [← code]
  exact canonical_refines (checkFunction_domain hs.2) (checkBoolPins_sound hs.1) k fd.body
    (state_entry (signatures F) H external (fd.params.map (·.1)) vs ws hd
      (by simpa using arity) fresh hb) scope

end IxCC.Own.Plain
