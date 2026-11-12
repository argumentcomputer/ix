import IxCC.Own.Plain.Proof.OwnedAccepts
import IxCC.Own.Plain.Check

/-! Bind the complete untrusted body map actually executed by every call. Today's check accepts
only the canonical producer's map; the ownership checker accepts that map
(`checkPlainMap_checkOwned`), and every map the checker accepts refines the source
(`checkOwned_refines`). Both landed statements are derived that way (heap stage 2); their text is
unchanged (checked by `rfl` against the derivations in `OwnedAccepts`). -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc

theorem checked_program_refines {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) :=
  checked_program_refines' checked k hf hd hb

theorem checked_contract_program_refines {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) :=
  checked_contract_program_refines' checked k hf hd hb

example : @checked_program_refines' = @checked_program_refines := rfl
example : @checked_contract_program_refines' = @checked_contract_program_refines := rfl

end IxCC.Own.Plain
