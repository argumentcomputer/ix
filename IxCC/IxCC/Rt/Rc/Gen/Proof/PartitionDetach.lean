import IxCC.Rt.Rc.Gen.Proof.PartitionAdvance
import IxCC.Rt.Rc.Gen.Proof.DetachHeap

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ArenaPartition.detach_pending {heap addresses base bump limit slots}
    (h : ArenaPartition cmax heap addresses base bump limit slots)
    {parent : Slot} (hp : parent ∈ slots) {location body}
    (hk : parent.kind = .live location)
    (hcell : heap.cell? location = some (.live 1 .dyn body))
    (suffix : List RVal) (predecessor : Word) :
    ArenaPartition cmax (setCell heap location .dead) addresses base bump limit
      (advanceSlots parent.address location suffix predecessor slots) := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hcell).1
  obtain ⟨oldRefs, oldBody, hc0, haddr0, hclass0⟩ := h.live parent hp location hk
  let f : Slot → Slot := fun slot => if slot.address = parent.address then
    {slot with kind := .pending location suffix predecessor} else slot
  have ha (s : Slot) : (f s).address = s.address := by simp [f]; split <;> rfl
  have hc (s : Slot) : (f s).cls = s.cls := by simp [f]; split <;> rfl
  change ArenaPartition cmax (setCell heap location .dead) addresses base bump limit (slots.map f)
  refine {
    bounds := h.bounds, valid := ?_, bounded := ?_, disjoint := ?_, accounted := ?_
    live := ?_, placed := ?_, pending := ?_ }
  · intro slot hm
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    simpa only [ha, hc] using h.valid old hmem
  · intro slot hm
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    simpa only [hc] using h.bounded old hmem
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
      obtain ⟨r, b, hd, had, hcls⟩ := h.live old hmem loc ho
      have hn : location ≠ loc := by
        intro eq
        subst loc
        rw [haddr0] at had
        exact he (Option.some.inj had).symm
      refine ⟨r, b, ?_, ?_, ?_⟩
      · simpa [setCell_cell heap location _ hl, hn] using hd
      · simpa only [ha] using had
      · simpa only [hc] using hcls
  · intro loc r b hnew
    obtain ⟨hne, hold⟩ := free_live_old hcell hnew
    obtain ⟨slot, hm, hkind⟩ := h.placed loc r b hold
    have he : slot.address ≠ parent.address := by
      intro he
      have eq := h.address_unique hm hp he
      subst slot
      rw [hk] at hkind
      have : location = loc := by simpa using hkind
      exact hne this
    exact ⟨f slot, List.mem_map.mpr ⟨slot, hm, rfl⟩, by simpa [f, he] using hkind⟩
  · intro slot hm loc values pred hkind
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    by_cases he : old.address = parent.address
    · have eq : location = loc ∧ suffix = values ∧ predecessor = pred := by simpa [f, he] using hkind
      rw [← eq.1]
      simp [setCell_cell heap location _ hl]
    · have hd := h.pending old hmem loc values pred (by simpa [f, he] using hkind)
      have hn : location ≠ loc := by
        intro eq
        subst loc
        rw [hcell] at hd
        cases hd
      simpa [setCell_cell heap location _ hl, hn] using hd


end IxCC.Rt.Rc.Gen
