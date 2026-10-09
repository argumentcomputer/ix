import Compilatrix.Own.Rc.Heap
import Compilatrix.Rt.Rc.Proof.LiveMemory

namespace Compilatrix.Rt.Rc.Procs
open Compilatrix.Own Compilatrix.Own.Rc

theorem ArenaPartition.update_count {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots)
    {location refs body} (hc : heap.cell? location = some (.live refs .dyn body))
    (newRefs : Nat) :
    ArenaPartition (setCell heap location (.live newRefs .dyn body)) addresses base bump limit slots := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hc).1
  refine {h with live := ?_, placed := ?_, pending := ?_}
  · intro slot hm loc hk
    obtain ⟨r, b, hcell, ha, hs⟩ := h.live slot hm loc hk
    by_cases he : location = loc
    · subst loc
      rw [hc] at hcell
      have eqs : refs = r ∧ body = b := by simpa using hcell
      have hb : body = b := eqs.2
      subst b
      exact ⟨newRefs, body, by simp [setCell_cell heap location _ hl], ha, hs⟩
    · exact ⟨r, b, by simpa [setCell_cell heap location _ hl, he] using hcell, ha, hs⟩
  · intro loc r b hcell
    by_cases he : location = loc
    · subst loc
      have eqs : newRefs = r ∧ body = b := by simpa [setCell_cell heap location _ hl] using hcell
      have hb : body = b := eqs.2
      subst b
      exact h.placed location refs body hc
    · apply h.placed loc r b
      simpa [setCell_cell heap location _ hl, he] using hcell
  · intro slot hm loc suffix predecessor hk
    have hd := h.pending slot hm loc suffix predecessor hk
    have he : location ≠ loc := by
      intro eq
      subst loc
      rw [hc] at hd
      cases hd
    simpa [setCell_cell heap location _ hl, he] using hd


end Compilatrix.Rt.Rc.Procs
