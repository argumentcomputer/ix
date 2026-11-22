import IxCC.Rt.Rc.Gen.Proof.AllocatorReady
import IxCC.Rt.Rc.Gen.Proof.ProtectedMetadata
import IxCC.Rt.Rc.Gen.Proof.AllocFree
import IxCC.Rt.Rc.Proof.AllocatorMetadata

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem headAddress_eq (context : Word) (cls : Nat) :
    headAddress context cls = freeHeadAddress context (UInt64.ofNat (cls)) := by
  simp only [headAddress, freeHeadAddress, UInt64.add_zero]
  change context + dispWord ((8 * cls : Nat) : Int) =
    context + UInt64.ofNat (cls) * 8
  rw [dispWord_ofNat, UInt64.ofNat_mul]
  rw [UInt64.mul_comm]
  rw [show UInt64.ofNat 8 = (8 : Word) by decide]

/-- The complete release frame is sufficient to retain the real allocator
metadata and arena permissions; no control-word preservation premise is
silently attached to the heap model. -/
theorem AllocatorReady.after_protected
    {heap heap' addresses addresses' before after external external' context base bump limit slots slots' lists lists'}
    (h : AllocatorReady cmax heap addresses before external context base bump limit slots lists)
    (hf : ProtectedFrame before after context base bump)
    (hi : ReleaseInvariant cmax heap' addresses' after external' none [] context base bump limit slots' lists') :
    AllocatorReady cmax heap' addresses' after external' context base bump limit slots' lists' := by
  refine {
    idle := hi
    context_lower := h.context_lower
    context_before := h.context_before
    bump_aligned := h.bump_aligned
    bump_word := ?_
    limit_word := ?_
    bump_writable := ?_
    arena_access := ?_ }
  · have hw := h.bump_word
    rw [bumpAddress_eq] at hw ⊢
    exact hf.context_word 40 hw (by have := h.idle.context_fit; omega) (by decide)
      h.context_lower (by have := h.context_before; omega)
  · have hw := h.limit_word
    rw [limitAddress_eq] at hw ⊢
    exact hf.context_word 32 hw (by have := h.idle.context_fit; omega) (by decide)
      (by have := h.context_lower; omega) (by have := h.context_before; omega)
  · intro j hj; rw [hf.writable]; exact h.bump_writable j hj
  · intro a hlo hhi
    rw [hf.readable, hf.writable]
    exact h.arena_access a hlo hhi





end IxCC.Rt.Rc.Gen
