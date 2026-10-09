import Compilatrix.Rt.Rc.Proof.ReleaseInvariant
import Compilatrix.Rt.Rc.Proof.PartitionRecycle
import Compilatrix.Rt.Rc.Proof.ObjectFrame
import Compilatrix.Rt.Rc.Proof.CursorPreserve

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

theorem ReleaseInvariant.recycle_slot_frame
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent slot : Slot} (hp : parent ∈ slots) (hs : slot ∈ slots) (hne : slot ≠ parent)
    (oldHead : Word) :
    ObjectFrame mem (recycleParent mem context (UInt64.ofNat parent.cls) parent.address oldHead)
      slot.address (8*slot.cls) := by
  have vp := h.partition.valid parent hp
  have vs := h.partition.valid slot hs
  have hb := h.partition.bounds
  have hd := h.partition.disjoint_members hs hp hne
  have hh := h.head_disjoint parent.cls vp.1 vp.2.1 slot hs
  have hfit : slot.address.toNat+8*slot.cls ≤ 2^64 := by omega
  have hpfit : parent.address.toNat+8 ≤ 2^64 := by omega
  have hsep : slot.address.toNat+8*slot.cls ≤ parent.address.toNat ∨
      parent.address.toNat+8 ≤ slot.address.toNat := by
    rcases hd with hd | hd <;> omega
  exact (objectFrame_write mem slot.address parent.address oldHead _ .w64 hfit hpfit hsep).trans
    (objectFrame_write (mem.write .w64 parent.address oldHead) slot.address
      (freeHeadAddress context (UInt64.ofNat parent.cls)) parent.address _ .w64 hfit
      (h.head_fit parent.cls vp.1 vp.2.1) hh.symm)

theorem CursorChain.frame {addresses heap before after frames}
    (h : CursorChain addresses heap before frames)
    (hf : ∀ frame ∈ frames,
      ObjectFrame before after frame.address (cellBytes frame.original.fields.length)) :
    CursorChain addresses heap after frames := by
  induction frames with
  | nil => trivial
  | cons frame tail ih =>
    obtain ⟨hd, hc, hfit, ht⟩ := h
    have hframe := hf frame (by simp)
    exact ⟨hd, hc.frame hframe.readable hframe.writable hframe.bytes_eq, hfit,
      ih ht (fun f hm => hf f (by simp [hm]))⟩



end Compilatrix.Rt.Rc.Procs
