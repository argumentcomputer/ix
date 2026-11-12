import IxCC.Rt.Rc.Gen.Proof.ReservePartition
import IxCC.Rt.Rc.Gen.Proof.ReleaseInvariant

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

def popFree (lists : Nat → List Word) (cls : Nat) : Nat → List Word :=
  fun other => if other = cls then (lists other).tail else lists other

theorem ReleaseInvariant.free_class_unique
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {other : Nat} (hm : target.address ∈ lists other) :
    other = target.cls := by
  obtain ⟨slot, hs, ha, hc, hk⟩ := h.free_placed other target.address hm
  have eq := h.partition.address_unique hs ht ha
  subst slot
  exact hc.symm

theorem ReleaseInvariant.pop_free_mem
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail) (other : Nat) (word : Word) :
    word ∈ popFree lists target.cls other ↔ word ∈ lists other ∧ word ≠ target.address := by
  by_cases he : other = target.cls
  · subst other
    have hn : target.address ∉ tail := by
      have hd := h.free_distinct target.cls
      rw [hhead] at hd
      exact (List.nodup_cons.mp hd).1
    simp only [popFree, if_pos rfl, hhead, List.tail_cons, ite_true]
    constructor
    · intro hm
      exact ⟨by simp [hm], by intro eq; subst word; exact hn hm⟩
    · rintro ⟨hm, hne⟩
      rcases List.mem_cons.mp hm with he | hm
      · exact False.elim (hne he)
      · exact hm
  · simp only [popFree, if_neg he]
    constructor
    · intro hm
      refine ⟨hm, ?_⟩
      intro eq
      subst word
      exact he (h.free_class_unique ht hm)
    · exact And.left

theorem ReleaseInvariant.reserve_free_exact
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail) :
    ∀ slot ∈ reserveSlots target.address slots,
      slot.kind = .free ↔ slot.address ∈ popFree lists target.cls slot.cls := by
  intro slot hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  by_cases he : old.address = target.address
  · have eq := h.partition.address_unique hold ht he
    subst old
    simp only [if_pos rfl]
    rw [h.pop_free_mem ht hhead]
    simp
  · simp only [if_neg he]
    rw [h.pop_free_mem ht hhead]
    exact ⟨fun hk => ⟨(h.free_exact old hold).mp hk, he⟩,
      fun hm => (h.free_exact old hold).mpr hm.1⟩

theorem ReleaseInvariant.reserve_free_placed
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail)
    {cls : Nat} {address : Word} (hm : address ∈ popFree lists target.cls cls) :
    ∃ slot ∈ reserveSlots target.address slots,
      slot.address = address ∧ slot.cls = cls ∧ slot.kind = .free := by
  obtain ⟨hold, hne⟩ := (h.pop_free_mem ht hhead cls address).mp hm
  obtain ⟨slot, hs, ha, hc, hk⟩ := h.free_placed cls address hold
  have he : slot.address ≠ target.address := by simpa only [ha] using hne
  exact ⟨slot, List.mem_map.mpr ⟨slot, hs, by simp [he]⟩, ha, hc, hk⟩





end IxCC.Rt.Rc.Gen
