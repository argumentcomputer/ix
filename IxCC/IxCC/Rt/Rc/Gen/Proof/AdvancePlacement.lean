import IxCC.Rt.Rc.Gen.Proof.PartitionAdvance
import IxCC.Rt.Rc.Gen.Proof.RecycleClasses

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

theorem ReleaseInvariant.advance_free_exact
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location oldSuffix predecessor}
    (hk : parent.kind = .pending location oldSuffix predecessor) (suffix : List Own.RVal) :
    ∀ slot ∈ advanceSlots parent.address location suffix predecessor slots,
      slot.kind = .free ↔ slot.address ∈ lists slot.cls := by
  intro slot hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  by_cases he : old.address = parent.address
  · have ho := h.partition.address_unique hold hp he
    subst old
    simp [h.pending_not_free hp (pending_ne_free hk) parent.cls]
  · simpa [he] using h.free_exact old hold

theorem ReleaseInvariant.advance_free_placed
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location oldSuffix predecessor}
    (hk : parent.kind = .pending location oldSuffix predecessor) (suffix : List Own.RVal)
    {cls : Nat} {address : Word} (hm : address ∈ lists cls) :
    ∃ slot ∈ advanceSlots parent.address location suffix predecessor slots,
      slot.address = address ∧ slot.cls = cls ∧ slot.kind = .free := by
  obtain ⟨slot, hs, ha, hc, hf⟩ := h.free_placed cls address hm
  have hne : slot.address ≠ parent.address := by
    intro had
    have heq := h.partition.address_unique hs hp had
    subst slot
    rw [hk] at hf
    cases hf
  exact ⟨slot, List.mem_map.mpr ⟨slot, hs, by simp [hne]⟩, ha, hc, hf⟩



end IxCC.Rt.Rc.Gen
