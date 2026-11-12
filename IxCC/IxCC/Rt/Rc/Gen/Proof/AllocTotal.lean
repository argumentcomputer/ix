import IxCC.Rt.Rc.Gen.Proof.ReserveFree
import IxCC.Rt.Rc.Gen.Proof.ReserveBump
import IxCC.Rt.Rc.Gen.Proof.AllocFailure

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

/-- Total allocation by layout: a reserved cell of the layout's class, from that class's free list
when it is not empty, else from the bump pointer when the class fits below the limit, else the heap
failure. The logical heap and all external tokens are unchanged in every success. -/
theorem AllocatorReady.reserve_total
    {cmax heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {L : CellLayout} {cls : Nat} (hL : L.ok = true) (hcl : L.cls? = some cls) (hcmax : cls ≤ cmax)
    (clock : Nat) :
    (∃ cell after next slots' lists',
      eval (allocProgram L) clock [] mem context = .ok ([cell], after) ∧
      AllocatorReady cmax heap addresses after external context base next limit slots' lists' ∧
      ∃ chosen ∈ slots', chosen.address = cell ∧ chosen.cls = cls ∧
        chosen.kind = .reserved ∧ WordAt after cell (dynamicHeader L.nobj cls L.tag 1)) ∨
    (lists cls = [] ∧ limit.toNat < bump.toNat+classBytes cls ∧
      eval (allocProgram L) clock [] mem context = .resource .heap) := by
  cases he : lists cls with
  | nil =>
    by_cases hs : bump.toNat+classBytes cls ≤ limit.toNat
    · obtain ⟨hev, hr, hw⟩ := h.reserve_bump hL hcl hcmax he hs clock
      exact Or.inl ⟨bump, _, _, _, lists, hev, hr,
        bumpSlot bump cls, by simp, rfl, rfl, rfl, hw⟩
    · exact Or.inr ⟨rfl, by omega, h.reserve_short hL hcl he (by omega) clock⟩
  | cons cell tail =>
    obtain ⟨target, ht, ha, hc, hk⟩ := h.idle.free_placed cls cell (by rw [he]; simp)
    have hh : lists target.cls = target.address :: tail := by rw [hc, ha]; exact he
    obtain ⟨hev, hr, hm, hw⟩ := h.reserve_free ht hh hc hL hcl clock
    exact Or.inl ⟨target.address, _, bump, _, _, hev, hr,
      {target with kind := .reserved}, hm, rfl, hc, rfl, hw⟩

end IxCC.Rt.Rc.Gen
