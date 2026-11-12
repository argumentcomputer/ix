import IxCC.Own.Plain.Proof.Candidate
import IxCC.Own.Plain.Proof.EvalShape
import IxCC.Own.Rc.Proof.LeakFreedom

/-! Compose independent actual-target shape preservation with checked source
refinement. Reclamation requires an older-field initial heap and no external
owners; balanced disconnected cycles are never admitted by this premise. -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc

theorem checked_program_shape {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) (hh : HeapOk H) {w : Fir.Val}
    (source : Fir.evalCall F k f ws = .ok w) :
    ∃ v after,
      evalCall { source := F, bodies := candidate } k f vs H = .ok (v, after) ∧
      Proof.Den after v w ∧ Balance after external [v] ∧ HeapOk after ∧
      H.size ≤ after.size ∧ ExternalPreserved H after external := by
  have related := checked_program_refines checked k hf hd hb
  rw [source] at related
  obtain ⟨v, after, success, den, balance, preserved⟩ := related.success
  have shape := call_heap_shape { source := F, bodies := candidate } k f H vs hh (dens_bounded hd)
  obtain ⟨heapShape, size, _⟩ := shape v after success
  exact ⟨v, after, success, den, balance, heapShape, size, preserved⟩

theorem checked_program_reclaims {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) (k : Nat)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hb : Balance H (fun _ => 0) vs)
    (hh : HeapOk H) {w : Fir.Val} (source : Fir.evalCall F k f ws = .ok w) :
    ∃ v after released,
      evalCall { source := F, bodies := candidate } k f vs H = .ok (v, after) ∧
      Proof.Den after v w ∧ dropAll after [v] = some released ∧
      ∀ l, l < released.size → released.cell? l = some .dead := by
  obtain ⟨v, after, success, den, balance, shape, _, _⟩ :=
    checked_program_shape checked k hf hd hb hh source
  obtain ⟨released, dropped, dead⟩ := dropAll_reclaims shape balance
  exact ⟨v, after, released, success, den, dropped, dead⟩

example : @checked_program_reclaims' = @checked_program_reclaims := rfl

end IxCC.Own.Plain
