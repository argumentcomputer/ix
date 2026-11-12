import IxCC.Rt.Rc.Gen.Proof.FreeTable

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

theorem ReleaseInvariant.pending_not_free
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (hk : parent.kind ≠ .free) (cls : Nat) :
    parent.address ∉ lists cls := by
  intro hm
  have hs := (h.pending_free_separation hp hk hm).2
  rcases hs with hs | hs <;> omega

theorem ReleaseInvariant.recycle_distinct
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (hk : parent.kind ≠ .free) (cls : Nat) :
    (pushFree lists parent.cls parent.address cls).Nodup := by
  by_cases hc : cls = parent.cls
  · simp only [pushFree, if_pos hc, List.nodup_cons]
    exact ⟨h.pending_not_free hp hk cls, h.free_distinct cls⟩
  · simpa only [pushFree, if_neg hc] using h.free_distinct cls

theorem ReleaseInvariant.recycle_free_exact
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) :
    ∀ slot ∈ recycleSlots parent.address slots,
      slot.kind = .free ↔ slot.address ∈ pushFree lists parent.cls parent.address slot.cls := by
  intro slot hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  by_cases he : old.address = parent.address
  · have ho := h.partition.address_unique hold hp he
    subst old
    simp [pushFree]
  · have hf := h.free_exact old hold
    by_cases hc : old.cls = parent.cls
    · simpa [he, pushFree, hc] using hf
    · simpa [he, pushFree, hc] using hf




end IxCC.Rt.Rc.Gen
