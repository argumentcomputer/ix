import Compilatrix.Rt.Rc.Proof.ReleasePoint
import Compilatrix.Rt.Rc.Proof.AdvanceDetailed
import Compilatrix.Rt.Rc.Proof.AdvanceDispatch

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

theorem ReleasePoint.resume_move {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) {top tail}
    (hn : p.current = none) (hf : p.frames = top :: tail)
    (hv : top.visited < top.original.fields.length) :
    ∃ next, p.Move addresses external context base bump limit next := by
  obtain ⟨hi, hr⟩ := hp
  have hi' : ReleaseInvariant p.heap addresses p.mem external none (top :: tail)
      context base bump limit p.slots p.lists := by simpa only [hn, hf] using hi
  have hr' : p.env[8]? = some top.address := by simpa only [hn, hf, cursorHead] using hr
  let cls := UInt64.ofNat (smallClass top.original.fields.length)
  let remaining := UInt64.ofNat (top.original.fields.length-top.visited)
  let env := (p.env.insert 9 remaining).insert 10 cls
  have h8 : env[8]? = some top.address := by
    simp only [env, Std.HashMap.getElem?_insert]
    exact hr'
  have h9 : env[9]? = some remaining := by simp only [env, Std.HashMap.getElem?_insert]; rfl
  have h10 : env[10]? = some cls := by simp only [env, Std.HashMap.getElem?_insert]; rfl
  have hdispatch := hi'.advance_dispatch p.env hr'
  have hdispatch' : Sem.Star (semStep releaseProgram) (releaseState p.mem context p.env 6 0) 0
      (releaseState p.mem context env 8 0) := by
    simpa only [if_neg (by omega : top.visited ≠ top.original.fields.length), env, cls, remaining] using hdispatch
  obtain ⟨word, hw, hstep, hcursor, hbalance⟩ := hi'.resume_step hv env h8 h10 h9
  obtain ⟨parent, hm, ha, hc, hiNext⟩ := hi'.advance_complete_details hv
  let next : ReleasePoint := {p with
    mem := resumeParent p.mem top.address remaining
    current := some top.original.fields[top.visited]
    frames := advanceFrame top :: tail
    slots := advanceSlots parent.address top.location (advanceFrame top).suffix (cursorHead tail) p.slots
    env := ((resumeEnv env cls remaining word).insert 1 word).insert 2 top.address}
  refine ⟨next, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, word, hw, ?_, ?_⟩
    · simpa only [next, remaining, ha] using hiNext
    · simp only [next, Std.HashMap.getElem?_insert]; rfl
    · simp only [next, Std.HashMap.getElem?_insert, cursorHead, advanceFrame]; rfl
  · simpa only [ReleasePoint.rank, next, hn, hf] using cutpoint_resume_decreases p.heap top tail hv
  · refine ⟨1, ?_⟩
    simpa [ReleasePoint.state, hn, next, cls, remaining]
      using hdispatch'.trans hstep
  · simp only [hn]
    exact ⟨rfl, by simpa only [next, hf, Option.toList_some, List.cons_append, List.nil_append] using
      (cursorTokens_advance top tail hv).symm⟩


end Compilatrix.Rt.Rc.Procs
