import IxCC.Rt.Rc.Proof.ReserveFrames
import IxCC.Rt.Rc.Proof.FreeTable

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem ReleaseInvariant.reserve_heads
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail)
    {fields : Nat} (hc : target.cls = smallClass fields) (tag : Nat)
    {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ 32) :
    WordAt (reserveFree mem context target.address (tail.headD 0) fields tag)
      (freeHeadAddress context (UInt64.ofNat cls))
      ((popFree lists target.cls cls).headD 0) := by
  have vt := h.partition.valid target ht
  have hb := h.partition.bounds
  have hfit : target.address.toNat+8 ≤ 2^64 := by omega
  have hs := h.head_disjoint cls hl hu target ht
  have hsep : (freeHeadAddress context (UInt64.ofNat cls)).toNat+8 ≤ target.address.toNat ∨
      target.address.toNat+8 ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat := by
    rcases hs with hs | hs <;> omega
  have first : WordAt (mem.write .w64 (headAddress context fields) (tail.headD 0))
      (freeHeadAddress context (UInt64.ofNat cls)) ((popFree lists target.cls cls).headD 0) := by
    by_cases he : cls = target.cls
    · subst cls
      simpa only [headAddress_eq, ← hc, popFree, if_pos rfl, hhead, List.tail_cons, ite_true] using
        wordAt_write64 (m := mem) (b := freeHeadAddress context (UInt64.ofNat target.cls)) (v := tail.headD 0)
          (h.free_heads target.cls hl hu).readable
    · have hd := freeHead_disjoint h.context_fit hu vt.2.1 he
      simpa only [headAddress_eq, ← hc, popFree, if_neg he] using
        (h.free_heads cls hl hu).write_disjoint
          (w := .w64) (a := freeHeadAddress context (UInt64.ofNat target.cls))
          (u := tail.headD 0) (h.head_fit target.cls vt.1 vt.2.1) (h.head_fit cls hl hu) hd
  exact first.write_disjoint (w := .w64) (a := target.address)
    (u := dynamicHeader fields (smallClass fields) tag 1) hfit (h.head_fit cls hl hu) hsep


end IxCC.Rt.Rc.Procs
