import IxCC.Own.Plain.Proof.Unfold
import IxCC.Own.Plain.Check
import IxCC.Own.Proof.Heap

/-! Bind canonical/accepted bodies to actual source function lookups. This
is structural certificate authority, separate from semantic refinement. -/

set_option autoImplicit false
namespace IxCC.Own.Plain

theorem canonical_body (P : Fir.Program) (f : Fir.FunId) :
    (Program.canonical P).bodies.get? f =
      (P.fun? f).map (fun fd => lowerCode (fd.params.map (·.1)) [] fd.body) := by
  exact Proof.get?_map _ P.funs f

theorem canonical_body_of {P : Fir.Program} {f : Fir.FunId} {fd : Fir.Fun}
    (h : P.fun? f = some fd) :
    (Program.canonical P).bodies.get? f = some (lowerCode (fd.params.map (·.1)) [] fd.body) := by
  rw [canonical_body, h]; rfl

theorem checked_body_is_canonical {P : Fir.Program} {f : Fir.FunId} {proposal : Code}
    (h : checkFunction P f proposal = true) :
    (Program.canonical P).bodies.get? f = some proposal := by
  obtain ⟨fd, _, hf, _, hb⟩ := checkFunction_parts h
  rw [canonical_body_of hf, ((checkBody_iff ..).mp hb).2.2]

theorem canonical_call {P : Fir.Program} {f : Fir.FunId} {fd : Fir.Fun}
    (h : P.fun? f = some fd) (clock : Nat) (vs : List RVal) (H : Heap) :
    evalCall (Program.canonical P) clock f vs H =
      callFun (Program.canonical P) clock fd (lowerCode (fd.params.map (·.1)) [] fd.body) vs H := by
  exact evalCall_of _ _ _ h (canonical_body_of h) vs


end IxCC.Own.Plain
