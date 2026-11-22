import IxCC.Rt.Rc.Proof.BumpFrames
import IxCC.Rt.Rc.Proof.ReserveChains
import IxCC.Rt.Rc.Proof.FreeTable

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem AllocatorReady.bump_chains
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields : Nat} (hpos : 0 < fields) (hspace : bump.toNat+cellBytes fields ≤ limit.toNat)
    (tag : Nat) (next : Word) (cls : Nat) :
    FreeChain (reserveBump mem context bump next fields tag) (lists cls) := by
  apply (h.idle.free_chains cls).frame_words
  intro address hm value hw
  obtain ⟨slot, hs, ha, hc, hk⟩ := h.idle.free_placed cls address hm
  have hv := h.idle.partition.valid slot hs
  have hf := h.bump_slot_frame hs hpos hspace tag next
  have hw' : WordAt mem (slot.address+UInt64.ofNat 0) value := by simpa [ha] using hw
  simpa [ha] using hf.word (offset := 0) (by omega) hw'

theorem AllocatorReady.bump_heads
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields : Nat} (hspace : bump.toNat+cellBytes fields ≤ limit.toNat)
    (tag : Nat) (next : Word) {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ 32) :
    WordAt (reserveBump mem context bump next fields tag)
      (freeHeadAddress context (UInt64.ofNat cls)) ((lists cls).headD 0) := by
  have hb := h.idle.partition.bounds
  have hc := h.context_before
  have hcl := h.context_lower
  have ha := h.bump_address_nat
  have hh := freeHead_toNat h.idle.context_fit hu
  have hbytes : 8 ≤ cellBytes fields := by simp [cellBytes]; omega
  have hf := h.idle.head_fit cls hl hu
  have first := (h.idle.free_heads cls hl hu).write_disjoint
    (w := .w64) (a := bumpAddress context) (u := next)
    (by simp only [X86.Width.bytes]; omega) hf (Or.inr (by simp only [X86.Width.bytes]; omega))
  exact first.write_disjoint (w := .w64) (a := bump)
    (u := dynamicHeader fields (smallClass fields) tag 1)
    (by simp only [X86.Width.bytes]; omega) hf (Or.inl (by omega))



end IxCC.Rt.Rc.Procs
