import IxCC.Rt.Rc.Proof.ProtectedOps
import IxCC.Rt.Rc.Proof.ReleasePoint
import IxCC.Rt.Rc.Proof.SharedStep

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ReleasePoint.shared_move_frame {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) {location rc body}
    (hc : p.current = some (.loc location))
    (hcell : p.heap.cell? location = some (.live (rc+2) .dyn body)) :
    ∃ next, p.Move addresses external context base bump limit next ∧
      ProtectedFrame p.mem next.mem context base bump := by
  obtain ⟨hi, hr⟩ := hp
  have hr' : ∃ word, valueWord addresses (.loc location) = some word ∧
      p.env[1]? = some word ∧ p.env[2]? = some (cursorHead p.frames) := by
    simpa only [hc] using hr
  obtain ⟨address, ha, h1, h2⟩ := hr'
  have hi' : ReleaseInvariant p.heap addresses p.mem external (some (.loc location)) p.frames
      context base bump limit p.slots p.lists := by simpa only [hc] using hi
  obtain ⟨hs, hiNext⟩ := hi'.shared_step hcell ha p.env h1 h2
  let next : ReleasePoint := {p with
    heap := setCell p.heap location (.live (rc+1) .dyn body)
    mem := storeCount p.mem address (UInt64.ofNat rc)
    current := none
    env := ((p.env.insert 3 (UInt64.ofNat (rc+1))).insert 4 (UInt64.ofNat rc)).insert 8 (cursorHead p.frames)}
  have hrelease : releaseOne p.heap (.loc location) (cursorTokens p.frames) =
      some (next.heap, cursorTokens p.frames) := by simp [releaseOne, hcell, next]
  refine ⟨next, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨hiNext, by simp only [next, Std.HashMap.getElem?_insert]; rfl⟩
  · change ReleaseLess (cutpointRank next.heap none p.frames) (cutpointRank p.heap p.current p.frames)
    rw [hc]
    apply cutpoint_release_decreases
    simpa using hrelease
  · refine ⟨0, ?_⟩
    simpa [ReleasePoint.state, hc, next] using hs
  · simpa only [hc, next, Option.toList_none, List.nil_append] using hrelease

  · exact hi'.count_protected hcell ha (UInt64.ofNat rc)


end IxCC.Rt.Rc.Procs
