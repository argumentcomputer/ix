import IxCC.Rt.Rc.Proof.ReserveFree
import IxCC.Rt.Rc.Proof.ReserveBump
import IxCC.Rt.Rc.Proof.AllocFailure

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

/-- Total valid-layout allocation: reuse requires no unused bump capacity;
otherwise the exact available byte count chooses reservation or heap failure.
The logical heap and all external field tokens are unchanged in every success. -/
theorem AllocatorReady.reserve_total
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields tag : Nat} (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag)
    (clock : Nat) :
    (∃ cell after next slots' lists',
      eval (allocProgram fields tag) clock [] mem context = .ok ([cell], after) ∧
      AllocatorReady heap addresses after external context base next limit slots' lists' ∧
      ∃ chosen ∈ slots', chosen.address = cell ∧ chosen.cls = smallClass fields ∧
        chosen.kind = .reserved ∧ WordAt after cell (dynamicHeader fields (smallClass fields) tag 1)) ∨
    (lists (smallClass fields) = [] ∧ limit.toNat < bump.toNat+cellBytes fields ∧
      eval (allocProgram fields tag) clock [] mem context = .resource .heap) := by
  cases he : lists (smallClass fields) with
  | nil =>
    by_cases hs : bump.toNat+cellBytes fields ≤ limit.toNat
    · obtain ⟨hev, hr, hw⟩ := h.reserve_bump hpos hsmall htag he hs clock
      exact Or.inl ⟨bump, _, _, _, lists, hev, hr,
        bumpSlot bump fields, by simp, rfl, rfl, rfl, hw⟩
    · exact Or.inr ⟨rfl, by omega, h.reserve_short hpos hsmall htag he (by omega) clock⟩
  | cons cell tail =>
    obtain ⟨target, ht, ha, hc, hk⟩ := h.idle.free_placed (smallClass fields) cell (by rw [he]; simp)
    have hh : lists target.cls = target.address :: tail := by rw [hc, ha]; exact he
    obtain ⟨hev, hr, hm, hw⟩ := h.reserve_free ht hh hc hpos hsmall htag clock
    exact Or.inl ⟨target.address, _, bump, _, _, hev, hr,
      {target with kind := .reserved}, hm, rfl, hc, rfl, hw⟩


end IxCC.Rt.Rc.Procs
