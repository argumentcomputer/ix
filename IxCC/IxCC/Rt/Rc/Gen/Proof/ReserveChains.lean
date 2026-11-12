import IxCC.Rt.Rc.Gen.Proof.ReserveFrames
import IxCC.Rt.Rc.Proof.ReserveChains

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem ReleaseInvariant.reserve_chains
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail)
    {L : CellLayout} {k : Nat} (hc : target.cls = k) (cls : Nat) :
    FreeChain (reserveFree mem context target.address (tail.headD 0) L k) (popFree lists target.cls cls) := by
  have hchain : FreeChain mem (popFree lists target.cls cls) := by
    by_cases he : cls = target.cls
    · subst cls
      have hold := h.free_chains target.cls
      rw [hhead] at hold
      simpa only [popFree, if_pos rfl, hhead, List.tail_cons, ite_true] using hold.2
    · simpa only [popFree, if_neg he] using h.free_chains cls
  apply hchain.frame_words
  intro address hm value hw
  obtain ⟨hold, hne⟩ := (h.pop_free_mem ht hhead cls address).mp hm
  obtain ⟨slot, hs, ha, hcls, hk⟩ := h.free_placed cls address hold
  have hneq : slot ≠ target := by intro eq; subst slot; exact hne ha.symm
  have hv := h.partition.valid slot hs
  have hf := h.reserve_slot_frame (L := L) ht hs hneq hc (tail.headD 0)
  have hw' : WordAt mem (slot.address+UInt64.ofNat 0) value := by simpa [ha] using hw
  simpa [ha] using hf.word (offset := 0) (by omega) hw'



end IxCC.Rt.Rc.Gen
