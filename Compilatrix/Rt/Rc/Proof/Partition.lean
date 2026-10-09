import Compilatrix.Rt.Rc.Proof.LiveMemory

/-! Reclamation changes slot classification, never its address/extent.
These lemmas preserve the actual region partition. Free-list bytes and
pending-cursor correspondence are additional loop-invariant components. -/
namespace Compilatrix.Rt.Rc.Procs
open Lir

def recycleSlots (target : Word) (slots : List Slot) : List Slot :=
  slots.map fun slot => if slot.address = target then {slot with kind := .free} else slot

theorem ArenaPartition.recycle {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots) (target : Word)
    (hn : ∀ slot ∈ slots, slot.address = target → ∀ location, slot.kind ≠ .live location) :
    ArenaPartition heap addresses base bump limit (recycleSlots target slots) := by
  let f : Slot → Slot := fun slot => if slot.address = target then {slot with kind := .free} else slot
  have ha (s : Slot) : (f s).address = s.address := by simp [f]; split <;> rfl
  have hc (s : Slot) : (f s).cls = s.cls := by simp [f]; split <;> rfl
  change ArenaPartition heap addresses base bump limit (slots.map f)
  refine {
    bounds := h.bounds
    valid := ?_
    disjoint := ?_
    accounted := ?_
    live := ?_
    placed := ?_
    pending := ?_ }
  · intro slot hm
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    simpa only [ha, hc] using h.valid old hmem
  · intro i j si sj hi hj hne
    obtain ⟨oi, hoi, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hi)
    obtain ⟨oj, hoj, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hj)
    simpa only [ha, hc] using h.disjoint i j oi oj hoi hoj hne
  · intro n hn0 hnb
    obtain ⟨slot, hm, hlo, hhi⟩ := h.accounted n hn0 hnb
    exact ⟨f slot, List.mem_map.mpr ⟨slot, hm, rfl⟩, by simpa only [ha] using hlo,
      by simpa only [ha, hc] using hhi⟩
  · intro slot hm location hk
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    have hold : old.kind = .live location := by
      by_cases he : old.address = target
      · simp [f, he] at hk
      · simpa [f, he] using hk
    simpa only [ha, hc] using h.live old hmem location hold
  · intro location refs body hcell
    obtain ⟨slot, hm, hk⟩ := h.placed location refs body hcell
    have he : slot.address ≠ target := by
      intro he
      exact hn slot hm he location hk
    exact ⟨f slot, List.mem_map.mpr ⟨slot, hm, rfl⟩, by simpa [f, he] using hk⟩
  · intro slot hm location suffix predecessor hk
    obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hm
    have hold : old.kind = .pending location suffix predecessor := by
      by_cases he : old.address = target
      · simp [f, he] at hk
      · simpa [f, he] using hk
    exact h.pending old hmem location suffix predecessor hold


end Compilatrix.Rt.Rc.Procs
