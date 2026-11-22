import IxCC.Rt.Rc.Gen.Proof.ReleaseInvariant
import IxCC.Rt.Rc.Gen.Proof.PartitionRecycle
import IxCC.Rt.Rc.Gen.Proof.ObjectFrame
import IxCC.Rt.Rc.Proof.Memory

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof

theorem ReleaseInvariant.count_slot_frame
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {target slot : Slot} (ht : target ∈ slots) (hs : slot ∈ slots) (hne : slot ≠ target)
    (count : Word) :
    ObjectFrame mem (storeCount mem target.address count) slot.address (8*classWords slot.cls) := by
  have vt := h.partition.valid target ht
  have vs := h.partition.valid slot hs
  have hb := h.partition.bounds
  have hd := h.partition.disjoint_members hs ht hne
  have ha4 : (target.address+4).toNat = target.address.toNat+4 :=
    addr_toNat (a := target.address) (i := 4) (by omega)
  apply objectFrame_write mem slot.address (target.address+4) count _ .w32
  · omega
  · simp only [X86.Width.bytes]; rw [ha4]; omega
  · simp only [X86.Width.bytes]; rw [ha4]
    rcases hd with hd | hd <;> omega

theorem CursorChain.update_count {addresses heap mem frames location refs body}
    (h : CursorChain addresses heap mem frames)
    (hc : heap.cell? location = some (.live refs .dyn body)) (newRefs : Nat) :
    CursorChain addresses (setCell heap location (.live newRefs .dyn body)) mem frames := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hc).1
  induction frames with
  | nil => trivial
  | cons frame tail ih =>
    obtain ⟨hd, hp, hfit, ht⟩ := h
    have he : location ≠ frame.location := by
      intro he
      rw [← he, hc] at hd
      cases hd
    exact ⟨by simpa [setCell_cell heap location _ hl, he] using hd, hp, hfit, ih ht⟩

theorem ReleaseInvariant.count_cursor_frame
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {location} (hk : target.kind = .live location)
    (count : Word) {frame : CursorFrame} (hm : frame ∈ frames) :
    ObjectFrame mem (storeCount mem target.address count)
      frame.address (cellBytesOf frame.original.ctor) := by
  obtain ⟨earlier, later, he⟩ := List.mem_iff_append.mp hm
  obtain ⟨slot, hs, ha, hc, hp⟩ := h.cursors_placed earlier frame later he
  have hne : slot ≠ target := by
    intro eq
    subst slot
    rw [hk] at hp
    cases hp
  have hf := h.count_slot_frame ht hs hne count
  simpa only [ha, hc, cellBytesOf] using hf




end IxCC.Rt.Rc.Gen
