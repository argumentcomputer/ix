import IxCC.Rt.Rc.Gen.Proof.BumpFrames
import IxCC.Rt.Rc.Gen.Proof.ReserveChains
import IxCC.Rt.Rc.Gen.Proof.FreeTable

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem AllocatorReady.bump_chains
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {L : CellLayout} {k : Nat} (hk1 : 1 ≤ k) (hspace : bump.toNat+classBytes k ≤ limit.toNat)
    (next : Word) (cls : Nat) :
    FreeChain (reserveBump mem context bump next L k) (lists cls) := by
  apply (h.idle.free_chains cls).frame_words
  intro address hm value hw
  obtain ⟨slot, hs, ha, hc, hk⟩ := h.idle.free_placed cls address hm
  have hv := h.idle.partition.valid slot hs
  have hf := h.bump_slot_frame (L := L) hs hk1 hspace next
  have hw' : WordAt mem (slot.address+UInt64.ofNat 0) value := by simpa [ha] using hw
  simpa [ha] using hf.word (offset := 0) (by omega) hw'

theorem AllocatorReady.bump_heads
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {L : CellLayout} {k : Nat} (hk : 1 ≤ k) (hspace : bump.toNat+classBytes k ≤ limit.toNat)
    (next : Word) {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ maxClass) :
    WordAt (reserveBump mem context bump next L k)
      (freeHeadAddress context (UInt64.ofNat cls)) ((lists cls).headD 0) := by
  have hb := h.idle.partition.bounds
  have hc := h.context_before
  have hcl := h.context_lower
  have ha := h.bump_address_nat
  have hh := freeHead_toNat h.idle.context_fit hu
  have hbytes : 8 ≤ classBytes k := by have := classWords_pos hk; unfold classBytes; omega
  have hf := h.idle.head_fit cls hl hu
  have first := (h.idle.free_heads cls hl hu).write_disjoint
    (w := .w64) (a := bumpAddress context) (u := next)
    (by simp only [X86.Width.bytes]; omega) hf (Or.inr (by simp only [X86.Width.bytes]; omega))
  exact first.write_disjoint (w := .w64) (a := bump)
    (u := dynamicHeader L.nobj k L.tag 1)
    (by simp only [X86.Width.bytes]; omega) hf (Or.inl (by omega))



end IxCC.Rt.Rc.Gen
