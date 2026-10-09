import Compilatrix.Rt.Rc.Proof.PointCurrent
import Compilatrix.Rt.Rc.Proof.PointResume
import Compilatrix.Rt.Rc.Proof.PointRecycle

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

theorem ReleasePoint.progress {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) :
    (p.current = none ∧ p.frames = []) ∨ ∃ next, p.Move addresses external context base bump limit next := by
  cases hc : p.current with
  | some value => exact Or.inr (ReleasePoint.current_move hp hc)
  | none =>
    cases hf : p.frames with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons top tail =>
      have hi := hp.1
      have hcursor : CursorChain addresses p.heap p.mem (top :: tail) := by
        simpa only [hf] using hi.cursors
      have hle := hcursor.2.1.visited_le
      by_cases he : top.visited = top.original.fields.length
      · exact Or.inr (ReleasePoint.recycle_move hp hc hf he)
      · exact Or.inr (ReleasePoint.resume_move hp hc hf (by omega))

theorem ReleasePoint.Move.dropAll_eq {addresses external context base bump limit before after}
    (h : ReleasePoint.Move addresses external context base bump limit before after) :
    dropAll before.heap (before.current.toList ++ cursorTokens before.frames) =
      dropAll after.heap (after.current.toList ++ cursorTokens after.frames) := by
  have hs := h.2.2.2
  cases hc : before.current with
  | none =>
    simp only [hc] at hs
    simp only [hc, Option.toList_none, List.nil_append]
    rw [hs.1, hs.2]
  | some value =>
    simp only [hc] at hs
    simp only [hc, Option.toList_some, List.cons_append, List.nil_append]
    rw [dropAll, hs]



end Compilatrix.Rt.Rc.Procs
