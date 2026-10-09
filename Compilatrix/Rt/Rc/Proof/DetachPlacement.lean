import Compilatrix.Rt.Rc.Proof.PartitionDetach
import Compilatrix.Rt.Rc.Proof.ReleaseInvariant

namespace Compilatrix.Rt.Rc.Procs
open Lir

theorem ReleaseInvariant.live_not_free
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location} (hk : parent.kind = .live location)
    (cls : Nat) : parent.address ∉ lists cls := by
  intro hm
  obtain ⟨slot, hs, ha, hc, hf⟩ := h.free_placed cls parent.address hm
  have heq := h.partition.address_unique hs hp ha
  subst slot
  rw [hk] at hf
  cases hf

theorem ReleaseInvariant.detach_free_exact
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location} (hk : parent.kind = .live location)
    (suffix : List Own.RVal) (predecessor : Word) :
    ∀ slot ∈ advanceSlots parent.address location suffix predecessor slots,
      slot.kind = .free ↔ slot.address ∈ lists slot.cls := by
  intro slot hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  by_cases he : old.address = parent.address
  · have ho := h.partition.address_unique hold hp he
    subst old
    simp [h.live_not_free hp hk parent.cls]
  · simpa [he] using h.free_exact old hold

theorem ReleaseInvariant.detach_free_placed
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location} (hk : parent.kind = .live location)
    (suffix : List Own.RVal) (predecessor : Word) {cls : Nat} {address : Word}
    (hm : address ∈ lists cls) :
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




end Compilatrix.Rt.Rc.Procs
