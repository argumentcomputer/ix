import IxCC.Rt.Rc.Proof.PartitionRecycle

namespace IxCC.Rt.Rc.Procs
open Lir

def advanceSlots (target : Word) (location : Nat) (suffix : List Own.RVal)
    (predecessor : Word) (slots : List Slot) : List Slot :=
  slots.map fun slot => if slot.address = target then
    {slot with kind := .pending location suffix predecessor} else slot

/-- Updating the unvisited suffix changes no occupied byte extent. The target
was already pending/dead, so no live placement can be lost. -/
theorem ArenaPartition.advance_pending {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots)
    {parent : Slot} (hp : parent ∈ slots) {location oldSuffix predecessor}
    (hk : parent.kind = .pending location oldSuffix predecessor) (suffix : List Own.RVal) :
    ArenaPartition heap addresses base bump limit
      (advanceSlots parent.address location suffix predecessor slots) := by
  let f : Slot → Slot := fun slot => if slot.address = parent.address then
    {slot with kind := .pending location suffix predecessor} else slot
  have ha (s : Slot) : (f s).address = s.address := by simp [f]; split <;> rfl
  have hc (s : Slot) : (f s).cls = s.cls := by simp [f]; split <;> rfl
  have hd : heap.cell? location = some .dead := h.pending parent hp location oldSuffix predecessor hk
  change ArenaPartition heap addresses base bump limit (slots.map f)
  refine {
    bounds := h.bounds, valid := ?_, disjoint := ?_, accounted := ?_
    live := ?_, placed := ?_, pending := ?_ }
  · intro slot hm
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    simpa only [ha, hc] using h.valid old hmem
  · intro i j si sj hi hj hne
    obtain ⟨oi, hoi, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hi)
    obtain ⟨oj, hoj, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hj)
    simpa only [ha, hc] using h.disjoint i j oi oj hoi hoj hne
  · intro n hn hb
    obtain ⟨slot, hm, hlo, hhi⟩ := h.accounted n hn hb
    exact ⟨f slot, List.mem_map.mpr ⟨slot, hm, rfl⟩, by simpa only [ha] using hlo,
      by simpa only [ha, hc] using hhi⟩
  · intro slot hm loc hkind
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    by_cases he : old.address = parent.address
    · simp [f, he] at hkind
    · have ho : old.kind = .live loc := by simpa [f, he] using hkind
      simpa only [ha, hc] using h.live old hmem loc ho
  · intro loc refs body hcell
    obtain ⟨slot, hm, hkind⟩ := h.placed loc refs body hcell
    have he : slot.address ≠ parent.address := by
      intro he
      have eq := h.address_unique hm hp he
      subst slot
      rw [hk] at hkind
      cases hkind
    exact ⟨f slot, List.mem_map.mpr ⟨slot, hm, rfl⟩, by simpa [f, he] using hkind⟩
  · intro slot hm loc values pred hkind
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    by_cases he : old.address = parent.address
    · have eq : location = loc ∧ suffix = values ∧ predecessor = pred := by simpa [f, he] using hkind
      simpa only [← eq.1] using hd
    · exact h.pending old hmem loc values pred (by simpa [f, he] using hkind)


end IxCC.Rt.Rc.Procs
