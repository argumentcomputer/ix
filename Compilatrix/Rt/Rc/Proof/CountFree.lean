import Compilatrix.Rt.Rc.Proof.AdvanceFree
import Compilatrix.Rt.Rc.Proof.CountFrames

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

theorem ReleaseInvariant.count_free_chains
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {location} (hk : target.kind = .live location)
    (count : Word) (cls : Nat) :
    FreeChain (storeCount mem target.address count) (lists cls) := by
  have vt := h.partition.valid target ht
  have hb := h.partition.bounds
  have ha4 : (target.address+4).toNat = target.address.toNat+4 :=
    addr_toNat (a := target.address) (i := 4) (by omega)
  apply (h.free_chains cls).write_frame (width := .w32)
  · simp only [X86.Width.bytes]; rw [ha4]; omega
  · intro address hm
    obtain ⟨slot, hs, had, hc, hf⟩ := h.free_placed cls address hm
    have vs := h.partition.valid slot hs
    rw [had] at vs
    omega
  · intro address hm
    obtain ⟨slot, hs, had, hc, hf⟩ := h.free_placed cls address hm
    have vs := h.partition.valid slot hs
    have hne : slot ≠ target := by
      intro eq
      subst slot
      rw [hk] at hf
      cases hf
    have hd := h.partition.disjoint_members hs ht hne
    rw [had] at hd
    simp only [X86.Width.bytes]; rw [ha4]
    rcases hd with hd | hd <;> omega

theorem ReleaseInvariant.count_free_heads
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) (count : Word)
    {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ 32) :
    WordAt (storeCount mem target.address count)
      (freeHeadAddress context (UInt64.ofNat cls)) ((lists cls).headD 0) := by
  have vt := h.partition.valid target ht
  have hb := h.partition.bounds
  have hs := h.head_disjoint cls hl hu target ht
  have ha4 : (target.address+4).toNat = target.address.toNat+4 :=
    addr_toNat (a := target.address) (i := 4) (by omega)
  apply (h.free_heads cls hl hu).write_disjoint
  · simp only [X86.Width.bytes]; rw [ha4]; omega
  · exact h.head_fit cls hl hu
  · simp only [X86.Width.bytes]; rw [ha4]
    rcases hs with hs | hs <;> omega



end Compilatrix.Rt.Rc.Procs
