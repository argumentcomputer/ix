import Compilatrix.Rt.Rc.Proof.ReleaseInvariant
import Compilatrix.Rt.Rc.Proof.PartitionRecycle

/-! Finished-parent release composition: free-list separation follows from
the actual live/pending/free partition, rather than a fresh semantic premise. -/
namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Proof

theorem ReleaseInvariant.pending_free_separation
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor)
    {cls : Nat} {address : Word} (ha : address ∈ lists cls) :
    address.toNat+8 ≤ 2^64 ∧
    (address.toNat+8 ≤ parent.address.toNat ∨ parent.address.toNat+8 ≤ address.toNat) := by
  obtain ⟨free, hm, he, hc, hf⟩ := h.free_placed cls address ha
  have hne : free ≠ parent := by
    intro heq
    subst free
    rw [hk] at hf
    cases hf
  have hd := h.partition.disjoint_members hm hp hne
  have vf := h.partition.valid free hm
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  rw [he] at hd vf
  constructor
  · omega
  · rcases hd with hd | hd <;> omega

theorem ReleaseInvariant.recycle_chain
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor)
    (hr : ∀ j < 8, mem.readable (parent.address+UInt64.ofNat j) = true) :
    FreeChain (recycleParent mem context (UInt64.ofNat parent.cls) parent.address
      ((lists parent.cls).headD 0)) (parent.address :: lists parent.cls) ∧
    ArenaPartition heap addresses base bump limit (recycleSlots parent.address slots) := by
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  have hcls : 1 ≤ parent.cls ∧ parent.cls ≤ 32 := ⟨vp.1, vp.2.1⟩
  have hparent : parent.address.toNat+8 ≤ 2^64 := by omega
  have hhead := h.head_fit parent.cls hcls.1 hcls.2
  have hsep := h.head_disjoint parent.cls hcls.1 hcls.2 parent hp
  refine ⟨?_, h.partition.recycle_pending hp hk⟩
  apply (h.free_chains parent.cls).recycle_push hr hparent hhead
  · rcases hsep with hs | hs
    · exact Or.inr hs
    · left; omega
  · intro a ha
    exact (h.pending_free_separation hp hk ha).1
  · intro a ha
    have hpsep := (h.pending_free_separation hp hk ha).2
    obtain ⟨free, hm, he, hc, hf⟩ := h.free_placed parent.cls a ha
    have vs := h.partition.valid free hm
    have hs := h.head_disjoint parent.cls hcls.1 hcls.2 free hm
    rw [he] at hs
    refine ⟨hpsep, ?_⟩
    rcases hs with hs | hs
    · exact Or.inr hs
    · left; omega



end Compilatrix.Rt.Rc.Procs
