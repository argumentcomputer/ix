import Compilatrix.Rt.Rc.Proof.PointImmediate
import Compilatrix.Rt.Rc.Proof.PointShared
import Compilatrix.Rt.Rc.Proof.PointUnique

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

/-- Progress for every represented current token, with no assumed operation
simulation. Balance rules out dead/static/zero-count locations, while the
actual value encoding classifies every other accepted token as immediate. -/
theorem ReleasePoint.current_move {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) {value}
    (hc : p.current = some value) :
    ∃ next, p.Move addresses external context base bump limit next := by
  classical
  by_cases hl : ∃ location, value = .loc location
  · obtain ⟨location, rfl⟩ := hl
    have hi := hp.1
    have hb : Balance p.heap external (.loc location :: cursorTokens p.frames) := by
      simpa only [hc, Option.toList_some, List.cons_append, List.nil_append] using hi.balance
    obtain ⟨refs, body, hcell, hpositive⟩ := balance_pending_live (location := location) hb (by simp)
    cases refs with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨_, address, ha, cell⟩ := hi.live.cell location 1 .dyn body hcell
        have hnonempty := cell.fields_positive
        cases he : body.fields with
        | nil => simp [he] at hnonempty
        | cons child suffix => exact ReleasePoint.unique_move hp hc hcell he
      | succ rc => exact ReleasePoint.shared_move hp hc hcell
  · exact ReleasePoint.immediate_move hp hc (by intro location eq; exact hl ⟨location, eq⟩)


end Compilatrix.Rt.Rc.Procs
