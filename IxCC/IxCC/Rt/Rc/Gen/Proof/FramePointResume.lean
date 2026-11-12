import IxCC.Rt.Rc.Gen.Proof.ProtectedOps
import IxCC.Rt.Rc.Gen.Proof.ReleasePoint
import IxCC.Rt.Rc.Gen.Proof.AdvanceDetailed
import IxCC.Rt.Rc.Gen.Proof.AdvanceDispatch

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ReleasePoint.resume_move_frame {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid cmax addresses external context base bump limit) {top tail}
    (hn : p.current = none) (hf : p.frames = top :: tail)
    (hv : top.visited < top.original.ctor.nobj) :
    ∃ next, p.Move cmax addresses external context base bump limit next ∧
      ProtectedFrame p.mem next.mem context base bump := by
  obtain ⟨hi, hr⟩ := hp
  have hi' : ReleaseInvariant cmax p.heap addresses p.mem external none (top :: tail)
      context base bump limit p.slots p.lists := by simpa only [hn, hf] using hi
  have hr' : p.env[8]? = some top.address := by simpa only [hn, hf, cursorHead] using hr
  have hlen : top.visited < top.original.fields.length := by
    have := hi'.cursors.2.1.arity; omega
  let scan := UInt64.ofNat top.original.ctor.nobj
  let remaining := UInt64.ofNat (top.original.ctor.nobj-top.visited)
  let env := (p.env.insert 9 remaining).insert 10 scan
  have h8 : env[8]? = some top.address := by
    simp only [env, Std.HashMap.getElem?_insert]
    exact hr'
  have h9 : env[9]? = some remaining := by simp only [env, Std.HashMap.getElem?_insert]; rfl
  have h10 : env[10]? = some scan := by simp only [env, Std.HashMap.getElem?_insert]; rfl
  have hdispatch := hi'.advance_dispatch p.env hr'
  have hdispatch' : Sem.Star (semStep releaseProgram) (releaseState p.mem context p.env 6 0) 0
      (releaseState p.mem context env 8 0) := by
    simpa only [show top.visited ≠ top.original.ctor.nobj by omega, ↓reduceIte, env, scan, remaining]
      using hdispatch
  obtain ⟨word, hw, hstep, hcursor, hbalance⟩ := hi'.resume_step hv hlen env h8 h10 h9
  obtain ⟨parent, hm, ha, hc, hiNext⟩ := hi'.advance_complete_details hv hlen
  let next : ReleasePoint := {p with
    mem := resumeParent p.mem top.address remaining
    current := some top.original.fields[top.visited]
    frames := advanceFrame top :: tail
    slots := advanceSlots parent.address top.location (advanceFrame top).suffix (cursorHead tail) p.slots
    env := ((resumeEnv env scan remaining word).insert 1 word).insert 2 top.address}
  refine ⟨next, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, word, hw, ?_, ?_⟩
    · simpa only [next, remaining, ha] using hiNext
    · simp only [next, Std.HashMap.getElem?_insert]; rfl
    · simp only [next, Std.HashMap.getElem?_insert, cursorHead, advanceFrame]; rfl
  · simpa only [ReleasePoint.rank, next, hn, hf] using cutpoint_resume_decreases p.heap top tail hlen
  · refine ⟨1, ?_⟩
    simpa [ReleasePoint.state, hn, next, scan, remaining]
      using hdispatch'.trans hstep
  · refine ⟨[], noScalars, ?_⟩
    simp only [hn]
    exact ⟨rfl, by simpa only [next, hf, Option.toList_some, List.cons_append, List.nil_append] using
      (cursorTokens_advance top tail hlen).symm⟩

  · simpa only [next, ha] using hi'.advance_protected hm remaining


end IxCC.Rt.Rc.Gen
