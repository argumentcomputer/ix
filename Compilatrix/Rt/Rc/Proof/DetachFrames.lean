import Compilatrix.Rt.Rc.Proof.CountFrames
import Compilatrix.Rt.Rc.Proof.RecycleFrames

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Proof

theorem ReleaseInvariant.detach_slot_frame
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target slot : Slot} (ht : target ∈ slots) (hs : slot ∈ slots) (hne : slot ≠ target)
    (hclass : 2 ≤ target.cls) (predecessor : Word) (fields : Nat) :
    ObjectFrame mem (detachParent mem target.address predecessor fields) slot.address (8*slot.cls) := by
  have vt := h.partition.valid target ht
  have vs := h.partition.valid slot hs
  have hb := h.partition.bounds
  have hd := h.partition.disjoint_members hs ht hne
  have ha8 : (target.address+8).toNat = target.address.toNat+8 :=
    addr_toNat (a := target.address) (i := 8) (by omega)
  have hfit : slot.address.toNat+8*slot.cls ≤ 2^64 := by omega
  have hw64 : (target.address+8).toNat+8 ≤ 2^64 := by rw [ha8]; omega
  have hw8 : target.address.toNat+1 ≤ 2^64 := by omega
  have sep64 : slot.address.toNat+8*slot.cls ≤ (target.address+8).toNat ∨
      (target.address+8).toNat+8 ≤ slot.address.toNat := by
    rw [ha8]; rcases hd with hd | hd <;> omega
  have sep8 : slot.address.toNat+8*slot.cls ≤ target.address.toNat ∨
      target.address.toNat+1 ≤ slot.address.toNat := by
    rcases hd with hd | hd <;> omega
  exact (objectFrame_write mem slot.address (target.address+8) predecessor _ .w64 hfit hw64 sep64).trans
    (objectFrame_write (mem.write .w64 (target.address+8) predecessor) slot.address
      target.address (UInt64.ofNat (fields-1)) _ .w8 hfit hw8 sep8)

theorem CursorChain.free_cell {addresses heap mem frames location refs body}
    (h : CursorChain addresses heap mem frames)
    (hc : heap.cell? location = some (.live refs .dyn body)) :
    CursorChain addresses (setCell heap location .dead) mem frames := by
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

theorem ReleaseInvariant.detach_cursor_frame
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {location} (hk : target.kind = .live location)
    (hclass : 2 ≤ target.cls) (predecessor : Word) (fields : Nat)
    {frame : CursorFrame} (hm : frame ∈ frames) :
    ObjectFrame mem (detachParent mem target.address predecessor fields)
      frame.address (cellBytes frame.original.fields.length) := by
  obtain ⟨earlier, later, he⟩ := List.mem_iff_append.mp hm
  obtain ⟨slot, hs, ha, hc, hp⟩ := h.cursors_placed earlier frame later he
  have hne : slot ≠ target := by
    intro eq
    subst slot
    rw [hk] at hp
    cases hp
  have hf := h.detach_slot_frame ht hs hne hclass predecessor fields
  simpa only [ha, hc, cellBytes, smallClass, Nat.add_comm] using hf




end Compilatrix.Rt.Rc.Procs
