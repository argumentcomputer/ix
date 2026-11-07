import IxCC.Rt.Rc.Proof.DetachFrames
import IxCC.Rt.Rc.Proof.AdvanceFree

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem ReleaseInvariant.detach_free_chains
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {location} (hk : target.kind = .live location)
    (hclass : 2 ≤ target.cls) (predecessor : Word) (fields cls : Nat) :
    FreeChain (detachParent mem target.address predecessor fields) (lists cls) := by
  have vt := h.partition.valid target ht
  have hb := h.partition.bounds
  have ha8 : (target.address+8).toNat = target.address.toNat+8 :=
    addr_toNat (a := target.address) (i := 8) (by omega)
  have sep : ∀ address ∈ lists cls,
      address.toNat+8 ≤ target.address.toNat ∨ target.address.toNat+8*target.cls ≤ address.toNat := by
    intro address hm
    obtain ⟨slot, hs, had, hc, hf⟩ := h.free_placed cls address hm
    have vs := h.partition.valid slot hs
    have hne : slot ≠ target := by
      intro eq
      subst slot
      rw [hk] at hf
      cases hf
    have hd := h.partition.disjoint_members hs ht hne
    rw [had] at hd
    rcases hd with hd | hd <;> omega
  have fit : ∀ address ∈ lists cls, address.toNat+8 ≤ 2^64 := by
    intro address hm
    obtain ⟨slot, hs, had, hc, hf⟩ := h.free_placed cls address hm
    have vs := h.partition.valid slot hs
    rw [had] at vs
    omega
  have first := (h.free_chains cls).write_frame (store := target.address+8)
    (value := predecessor) (width := .w64)
    (by simp only [X86.Width.bytes]; rw [ha8]; omega) fit
    (by intro address hm; simp only [X86.Width.bytes]; rw [ha8]
        rcases sep address hm with hs | hs <;> omega)
  exact first.write_frame (store := target.address) (value := UInt64.ofNat (fields-1))
    (width := .w8) (by simp only [X86.Width.bytes]; omega) fit
    (by intro address hm; simp only [X86.Width.bytes]
        rcases sep address hm with hs | hs <;> omega)

theorem ReleaseInvariant.detach_free_heads
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) (hclass : 2 ≤ target.cls)
    (predecessor : Word) (fields : Nat) {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ 32) :
    WordAt (detachParent mem target.address predecessor fields)
      (freeHeadAddress context (UInt64.ofNat cls)) ((lists cls).headD 0) := by
  have vt := h.partition.valid target ht
  have hb := h.partition.bounds
  have hs := h.head_disjoint cls hl hu target ht
  have ha8 : (target.address+8).toNat = target.address.toNat+8 :=
    addr_toNat (a := target.address) (i := 8) (by omega)
  have first := (h.free_heads cls hl hu).write_disjoint
    (a := target.address+8) (u := predecessor) (w := .w64)
    (by simp only [X86.Width.bytes]; rw [ha8]; omega) (h.head_fit cls hl hu)
    (by simp only [X86.Width.bytes]; rw [ha8]; rcases hs with hs | hs <;> omega)
  exact first.write_disjoint (a := target.address) (u := UInt64.ofNat (fields-1))
    (w := .w8) (by simp only [X86.Width.bytes]; omega) (h.head_fit cls hl hu)
    (by simp only [X86.Width.bytes]; rcases hs with hs | hs <;> omega)



end IxCC.Rt.Rc.Procs
