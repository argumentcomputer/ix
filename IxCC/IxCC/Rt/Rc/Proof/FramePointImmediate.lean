import IxCC.Rt.Rc.Proof.ProtectedOps
import IxCC.Rt.Rc.Proof.ReleasePoint
import IxCC.Rt.Rc.Proof.ImmediateStep

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ReleasePoint.immediate_move_frame {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) {value : RVal}
    (hc : p.current = some value) (hn : ∀ location, value ≠ .loc location) :
    ∃ next, p.Move addresses external context base bump limit next ∧
      ProtectedFrame p.mem next.mem context base bump := by
  obtain ⟨hi, hr⟩ := hp
  have hr' : ∃ word, valueWord addresses value = some word ∧
      p.env[1]? = some word ∧ p.env[2]? = some (cursorHead p.frames) := by
    simpa only [hc] using hr
  obtain ⟨word, hw, h1, h2⟩ := hr'
  have hi' : ReleaseInvariant p.heap addresses p.mem external (some value) p.frames
      context base bump limit p.slots p.lists := by simpa only [hc] using hi
  obtain ⟨hs, hiNext⟩ := hi'.immediate_step hn word hw p.env h1 h2
  let next : ReleasePoint := {p with current := none, env := p.env.insert 8 (cursorHead p.frames)}
  have hrelease : releaseOne p.heap value (cursorTokens p.frames) =
      some (p.heap, cursorTokens p.frames) := by
    cases value with
    | loc l => exact False.elim (hn l rfl)
    | lit l => rfl
    | ctor0 c => rfl
    | erased => rfl
  refine ⟨next, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨hiNext, by simp only [next, Std.HashMap.getElem?_insert]; rfl⟩
  · change ReleaseLess (cutpointRank p.heap none p.frames) (cutpointRank p.heap p.current p.frames)
    rw [hc]
    apply cutpoint_release_decreases
    simpa using hrelease
  · refine ⟨0, ?_⟩
    simpa [ReleasePoint.state, hc, next] using hs
  · simpa only [hc, next, Option.toList_none, List.nil_append] using hrelease

  · exact ProtectedFrame.refl p.mem context base bump


end IxCC.Rt.Rc.Procs
