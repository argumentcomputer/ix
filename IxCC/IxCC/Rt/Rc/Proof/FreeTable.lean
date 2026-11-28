import IxCC.Rt.Rc.Proof.RecycleStep

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def pushFree (lists : Nat → List Word) (cls : Nat) (address : Word) : Nat → List Word :=
  fun other => if other = cls then address :: lists other else lists other

theorem freeHead_toNat {context : Word} {cls : Nat}
    (hctx : context.toNat+8*33 < 2^63) (hc : cls ≤ 32) :
    (freeHeadAddress context (UInt64.ofNat cls)).toNat = context.toNat+8*cls := by
  have hn : (UInt64.ofNat cls).toNat = cls := toNat_ofNat_lt (by omega)
  have hm : (UInt64.ofNat cls*8).toNat = 8*cls := by
    rw [UInt64.toNat_mul, hn]
    change (cls*8) % 2^64 = 8*cls
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  unfold freeHeadAddress
  rw [UInt64.toNat_add, hm]
  exact Nat.mod_eq_of_lt (by omega)

theorem freeHead_disjoint {context : Word} {left right : Nat}
    (hctx : context.toNat+8*33 < 2^63) (hl : left ≤ 32) (hr : right ≤ 32)
    (hne : left ≠ right) :
    (freeHeadAddress context (UInt64.ofNat left)).toNat+8 ≤
      (freeHeadAddress context (UInt64.ofNat right)).toNat ∨
    (freeHeadAddress context (UInt64.ofNat right)).toNat+8 ≤
      (freeHeadAddress context (UInt64.ofNat left)).toNat := by
  rw [freeHead_toNat hctx hl, freeHead_toNat hctx hr]
  omega

theorem ReleaseInvariant.recycle_heads
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (oldHead : Word)
    {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ 32) :
    WordAt (recycleParent mem context (UInt64.ofNat parent.cls) parent.address oldHead)
      (freeHeadAddress context (UInt64.ofNat cls))
      ((pushFree lists parent.cls parent.address cls).headD 0) := by
  have vp := h.partition.valid parent hp
  have hb := h.partition.bounds
  have hfit : parent.address.toNat+8 ≤ 2^64 := by omega
  by_cases he : cls = parent.cls
  · subst cls
    simp only [pushFree, if_pos rfl, List.headD_cons]
    exact recycled_head (h.free_heads parent.cls hl hu).readable
  · have hs := h.head_disjoint cls hl hu parent hp
    have hsep : (freeHeadAddress context (UInt64.ofNat cls)).toNat+8 ≤ parent.address.toNat ∨
        parent.address.toNat+8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat := by
      rcases hs with hs | hs <;> omega
    have hw := (h.free_heads cls hl hu).write_disjoint
      (w := .w64) (a := parent.address) (u := oldHead) hfit (h.head_fit cls hl hu) hsep
    have hd := freeHead_disjoint h.context_fit hu vp.2.1 he
    simpa only [pushFree, if_neg he, recycleParent] using
      hw.write_disjoint (h.head_fit parent.cls vp.1 vp.2.1) (h.head_fit cls hl hu) hd




end IxCC.Rt.Rc.Procs
