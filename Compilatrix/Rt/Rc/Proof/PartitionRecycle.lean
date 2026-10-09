import Compilatrix.Rt.Rc.Proof.Partition

namespace Compilatrix.Rt.Rc.Procs
open Lir

/-- Positive disjoint slot extents rule out aliasing addresses, including
aliasing between a pending parent and a surviving live cell. -/
theorem ArenaPartition.address_unique {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots)
    {left right : Slot} (hl : left ∈ slots) (hr : right ∈ slots)
    (he : left.address = right.address) : left = right := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  by_cases hij : i = j
  · subst j
    rw [hi] at hj
    exact Option.some.inj hj
  · have hd := h.disjoint i j left right hi hj hij
    have hcl := (h.valid left hl).1
    have hcr := (h.valid right hr).1
    rw [he] at hd
    rcases hd with hd | hd <;> omega

/-- Actual pending membership discharges recycle's no-live-target premise;
it is not a separate caller-supplied preservation assertion. -/
theorem ArenaPartition.recycle_pending {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor) :
    ArenaPartition heap addresses base bump limit (recycleSlots parent.address slots) := by
  apply h.recycle
  intro slot hm ha liveLocation hlive
  have he := h.address_unique hm hp ha
  subst slot
  rw [hk] at hlive
  cases hlive




theorem ArenaPartition.disjoint_members {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots)
    {left right : Slot} (hl : left ∈ slots) (hr : right ∈ slots) (hne : left ≠ right) :
    left.address.toNat+8*left.cls ≤ right.address.toNat ∨
      right.address.toNat+8*right.cls ≤ left.address.toNat := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  apply h.disjoint i j left right hi hj
  intro he
  subst j
  rw [hi] at hj
  exact hne (Option.some.inj hj)


end Compilatrix.Rt.Rc.Procs
