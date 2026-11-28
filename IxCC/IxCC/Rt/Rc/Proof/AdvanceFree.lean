import IxCC.Rt.Rc.Proof.RecycleStep

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem FreeChain.write_frame {mem : X86.Memory} {store value : Word} {width : X86.Width}
    {chain : List Word} (h : FreeChain mem chain)
    (hs : store.toNat+width.bytes ≤ 2^64)
    (hfit : ∀ address ∈ chain, address.toNat+8 ≤ 2^64)
    (hsep : ∀ address ∈ chain,
      address.toNat+8 ≤ store.toNat ∨ store.toNat+width.bytes ≤ address.toNat) :
    FreeChain (mem.write width store value) chain := by
  induction chain with
  | nil => trivial
  | cons address tail ih =>
    obtain ⟨hw, ht⟩ := h
    refine ⟨hw.write_disjoint hs (hfit address (by simp)) (hsep address (by simp)), ?_⟩
    exact ih ht (fun a ha => hfit a (by simp [ha])) (fun a ha => hsep a (by simp [ha]))

theorem ReleaseInvariant.advance_chains
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor) (remaining : Word) (cls : Nat) :
    FreeChain (resumeParent mem parent.address remaining) (lists cls) := by
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  apply (h.free_chains cls).write_frame (width := .w8)
  · simp only [X86.Width.bytes]; omega
  · intro address ha
    exact (h.pending_free_separation hp hk ha).1
  · intro address ha
    have hs := (h.pending_free_separation hp hk ha).2
    simp only [X86.Width.bytes]
    rcases hs with hs | hs <;> omega

theorem ReleaseInvariant.advance_heads
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (remaining : Word)
    {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ 32) :
    WordAt (resumeParent mem parent.address remaining)
      (freeHeadAddress context (UInt64.ofNat cls)) ((lists cls).headD 0) := by
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  have hs := h.head_disjoint cls hl hu parent hp
  apply (h.free_heads cls hl hu).write_disjoint
  · simp only [X86.Width.bytes]; omega
  · exact h.head_fit cls hl hu
  · simp only [X86.Width.bytes]
    rcases hs with hs | hs <;> omega




end IxCC.Rt.Rc.Procs
