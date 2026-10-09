import Compilatrix.Rt.Rc.Proof.PartitionRecycle

namespace Compilatrix.Rt.Rc.Procs
open Lir

def reserveSlots (address : Word) (slots : List Slot) : List Slot :=
  slots.map fun slot => if slot.address = address then {slot with kind := .reserved} else slot

theorem ArenaPartition.reserve_free {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots)
    {target : Slot} (ht : target ∈ slots) (hk : target.kind = .free) :
    ArenaPartition heap addresses base bump limit (reserveSlots target.address slots) := by
  let f : Slot → Slot := fun s => if s.address = target.address then {s with kind := .reserved} else s
  have ha (s : Slot) : (f s).address = s.address := by simp [f]; split <;> rfl
  have hc (s : Slot) : (f s).cls = s.cls := by simp [f]; split <;> rfl
  change ArenaPartition heap addresses base bump limit (slots.map f)
  refine {
    bounds := h.bounds, valid := ?_, disjoint := ?_, accounted := ?_
    live := ?_, placed := ?_, pending := ?_ }
  · intro slot hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    simpa only [ha, hc] using h.valid old hold
  · intro i j si sj hi hj hne
    obtain ⟨oi, hoi, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hi)
    obtain ⟨oj, hoj, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hj)
    simpa only [ha, hc] using h.disjoint i j oi oj hoi hoj hne
  · intro n hlo hhi
    obtain ⟨slot, hm, hl, hh⟩ := h.accounted n hlo hhi
    exact ⟨f slot, List.mem_map.mpr ⟨slot, hm, rfl⟩, by simpa only [ha] using hl,
      by simpa only [ha, hc] using hh⟩
  · intro slot hm loc hkind
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    by_cases he : old.address = target.address
    · simp [f, he] at hkind
    · simpa only [f, if_neg he] using h.live old hold loc (by simpa [f, he] using hkind)
  · intro loc refs body hcell
    obtain ⟨slot, hm, hkind⟩ := h.placed loc refs body hcell
    have he : slot.address ≠ target.address := by
      intro he
      have eq := h.address_unique hm ht he
      subst slot
      rw [hk] at hkind
      cases hkind
    exact ⟨slot, List.mem_map.mpr ⟨slot, hm, by simp [f, he]⟩, hkind⟩
  · intro slot hm loc suffix pred hkind
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    by_cases he : old.address = target.address
    · simp [f, he] at hkind
    · exact h.pending old hold loc suffix pred (by simpa [f, he] using hkind)


end Compilatrix.Rt.Rc.Procs
