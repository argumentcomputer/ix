import Compilatrix.Rt.Rc.Proof.ProtectedOps
import Compilatrix.Rt.Rc.Proof.ReleasePoint
import Compilatrix.Rt.Rc.Proof.UniqueStep

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

theorem ReleasePoint.unique_move_frame {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) {location body child suffix}
    (hc : p.current = some (.loc location))
    (hcell : p.heap.cell? location = some (.live 1 .dyn body))
    (hfields : body.fields = child :: suffix) :
    ∃ next, p.Move addresses external context base bump limit next ∧
      ProtectedFrame p.mem next.mem context base bump := by
  obtain ⟨hi, hr⟩ := hp
  have hr' : ∃ word, valueWord addresses (.loc location) = some word ∧
      p.env[1]? = some word ∧ p.env[2]? = some (cursorHead p.frames) := by
    simpa only [hc] using hr
  obtain ⟨address, ha, h1, h2⟩ := hr'
  have hi' : ReleaseInvariant p.heap addresses p.mem external (some (.loc location)) p.frames
      context base bump limit p.slots p.lists := by simpa only [hc] using hi
  obtain ⟨parent, hm, word, hw, hs, hiNext⟩ := hi'.unique_step hcell ha hfields p.env h1 h2
  let next : ReleasePoint := {p with
    heap := setCell p.heap location .dead
    mem := detachParent p.mem address (cursorHead p.frames) body.fields.length
    current := some child
    frames := detachFrame location address body p.mem :: p.frames
    slots := advanceSlots parent.address location suffix (cursorHead p.frames) p.slots
    env := ((detachEnv (p.env.insert 3 0) body.fields.length word).insert 1 word).insert 2 address}
  have hrelease : releaseOne p.heap (.loc location) (cursorTokens p.frames) =
      some (next.heap, next.current.toList ++ cursorTokens next.frames) := by
    simp [releaseOne, hcell, next, cursorTokens, detachFrame, CursorFrame.suffix, flattenPending, hfields]
  refine ⟨next, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨hiNext, word, hw, ?_, ?_⟩
    · simp only [next, Std.HashMap.getElem?_insert]; rfl
    · simp only [next, Std.HashMap.getElem?_insert, cursorHead, detachFrame]; rfl
  · change ReleaseLess (cutpointRank next.heap next.current next.frames)
      (cutpointRank p.heap p.current p.frames)
    rw [hc]
    exact cutpoint_release_decreases hrelease
  · refine ⟨1, ?_⟩
    simpa only [ReleasePoint.state, hc, next, Option.isSome_some, ite_true] using hs
  · simpa only [hc] using hrelease

  · exact hi'.detach_protected hcell ha (cursorHead p.frames)


end Compilatrix.Rt.Rc.Procs
