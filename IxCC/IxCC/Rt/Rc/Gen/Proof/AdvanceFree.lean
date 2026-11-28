import IxCC.Rt.Rc.Gen.Proof.RecycleStep
import IxCC.Rt.Rc.Proof.AdvanceFree

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem ReleaseInvariant.advance_chains
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor) (remaining : Word) (cls : Nat) :
    FreeChain (resumeParent mem parent.address remaining) (lists cls) := by
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  have h4 : (parent.address+4).toNat = parent.address.toNat+4 :=
    addr_toNat (a := parent.address) (i := 4) (by omega)
  apply (h.free_chains cls).write_frame (width := .w32)
  · simp only [X86.Width.bytes]; omega
  · intro address ha
    exact (h.pending_free_separation hp (pending_ne_free hk) ha).1
  · intro address ha
    have hs := (h.pending_free_separation hp (pending_ne_free hk) ha).2
    simp only [X86.Width.bytes, h4]
    rcases hs with hs | hs <;> omega

theorem ReleaseInvariant.advance_heads
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (remaining : Word)
    {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ maxClass) :
    WordAt (resumeParent mem parent.address remaining)
      (freeHeadAddress context (UInt64.ofNat cls)) ((lists cls).headD 0) := by
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  have hs := h.head_disjoint cls hl hu parent hp
  have h4 : (parent.address+4).toNat = parent.address.toNat+4 :=
    addr_toNat (a := parent.address) (i := 4) (by omega)
  apply (h.free_heads cls hl hu).write_disjoint
  · simp only [X86.Width.bytes, h4]; omega
  · exact h.head_fit cls hl hu
  · simp only [X86.Width.bytes, h4]
    rcases hs with hs | hs <;> omega

end IxCC.Rt.Rc.Gen
