import IxCC.Rt.Rc.Gen.Proof.FramePointCurrent
import IxCC.Rt.Rc.Gen.Proof.FramePointResume
import IxCC.Rt.Rc.Gen.Proof.FramePointRecycle

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ReleasePoint.progress_frame {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid cmax addresses external context base bump limit) :
    (p.current = none ∧ p.frames = []) ∨ ∃ next, p.Move cmax addresses external context base bump limit next ∧
      ProtectedFrame p.mem next.mem context base bump := by
  cases hc : p.current with
  | some value => exact Or.inr (ReleasePoint.current_move_frame hp hc)
  | none =>
    cases hf : p.frames with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons top tail =>
      have hi := hp.1
      have hcursor : CursorChain addresses p.heap p.mem (top :: tail) := by
        simpa only [hf] using hi.cursors
      have hle := hcursor.2.1.visited_le
      by_cases he : top.visited = top.original.ctor.nobj
      · exact Or.inr (ReleasePoint.recycle_move_frame hp hc hf he)
      · exact Or.inr (ReleasePoint.resume_move_frame hp hc hf (by omega))


end IxCC.Rt.Rc.Gen
