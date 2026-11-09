import IxCC.Own.Plain.Proof.Checked
import IxCC.Own.Plain.Check

/-! Bind the complete untrusted body map actually executed by every call.
This deliberately conservative exact-image check also fixes trie shape;
missing, extra, and changed entries cannot hide behind root-only checking. -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc

theorem checked_program_refines {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) := by
  obtain ⟨domain, pins, bound⟩ := checkPlainMap_parts checked
  rw [bound]
  exact canonical_call_refines domain pins k hf hd hb

theorem checked_contract_program_refines {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) := by
  obtain ⟨domain, pins, bound⟩ := checkContractPlainMap_parts checked
  rw [bound]
  exact canonical_contract_call_refines domain pins k hf hd hb

end IxCC.Own.Plain
