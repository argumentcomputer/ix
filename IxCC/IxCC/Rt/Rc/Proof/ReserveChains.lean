import IxCC.Rt.Rc.Proof.ReserveFrames

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem FreeChain.frame_words {before after : X86.Memory} {chain : List Word}
    (h : FreeChain before chain)
    (hf : ∀ address ∈ chain, ∀ value, WordAt before address value → WordAt after address value) :
    FreeChain after chain := by
  induction chain with
  | nil => trivial
  | cons address tail ih =>
    exact ⟨hf address (by simp) _ h.1,
      ih h.2 (fun a hm v hw => hf a (by simp [hm]) v hw)⟩

theorem ReleaseInvariant.reserve_chains
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail)
    {fields : Nat} (hc : target.cls = smallClass fields) (tag : Nat) (cls : Nat) :
    FreeChain (reserveFree mem context target.address (tail.headD 0) fields tag) (popFree lists target.cls cls) := by
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
  have hf := h.reserve_slot_frame ht hs hneq hc tag (tail.headD 0)
  have hw' : WordAt mem (slot.address+UInt64.ofNat 0) value := by simpa [ha] using hw
  simpa [ha] using hf.word (offset := 0) (by omega) hw'



end IxCC.Rt.Rc.Procs
