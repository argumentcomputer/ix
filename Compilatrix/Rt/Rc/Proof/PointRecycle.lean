import Compilatrix.Rt.Rc.Proof.ReleasePoint
import Compilatrix.Rt.Rc.Proof.RecycleDetailed
import Compilatrix.Rt.Rc.Proof.AdvanceDispatch

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

theorem ReleasePoint.recycle_move {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) {top tail}
    (hn : p.current = none) (hf : p.frames = top :: tail)
    (hv : top.visited = top.original.fields.length) :
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
  have h10 : env[10]? = some cls := by simp only [env, Std.HashMap.getElem?_insert]; rfl
  have hdispatch := hi'.advance_dispatch p.env hr'
  have hdispatch' : Sem.Star (semStep releaseProgram) (releaseState p.mem context p.env 6 0) 0
      (releaseState p.mem context env 9 0) := by
    simpa only [if_pos hv, env, cls, remaining] using hdispatch
  obtain ⟨parent, hm, ha, hc, hiNext⟩ := hi'.recycle_complete_details hv
  have vp := hi'.partition.valid parent hm
  have hpred : loadWord p.mem .w64 .zero (parent.address+8) = some (cursorHead tail) := by
    rw [ha]
    simp only [loadWord, hi'.cursors.2.1.link.read64]
  have hhead := hi'.free_heads parent.cls vp.1 vp.2.1
  have hload : loadWord p.mem .w64 .zero (freeHeadAddress context (UInt64.ofNat parent.cls)) =
      some ((p.lists parent.cls).headD 0) := by simp only [loadWord, hhead.read64]
  have hwrite : ∀ j < 8, p.mem.writable (parent.address+UInt64.ofNat j) = true := by
    intro j hj
    rw [ha]
    apply (hi'.cursor_access top (by simp) j ?_).2
    simp only [cellBytes]
    omega
  have hstep := finished_parent_recycle p.mem context (UInt64.ofNat parent.cls) parent.address
    (cursorHead tail) ((p.lists parent.cls).headD 0) env (by simpa only [ha] using h8)
    (by simpa only [hc, cls] using h10) hpred hload hwrite
    (hi'.head_writable parent.cls vp.1 vp.2.1)
  let next : ReleasePoint := {p with
    mem := recycleParent p.mem context (UInt64.ofNat parent.cls) parent.address ((p.lists parent.cls).headD 0)
    frames := tail
    slots := recycleSlots parent.address p.slots
    lists := pushFree p.lists parent.cls parent.address
    env := ((env.insert 15 (cursorHead tail)).insert 16 ((p.lists parent.cls).headD 0)).insert 8 (cursorHead tail)}
  refine ⟨next, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [next, hn] using hiNext
    · simp only [next, hn, Std.HashMap.getElem?_insert]; rfl
  · simpa only [ReleasePoint.rank, next, hn, hf] using cutpoint_recycle_decreases p.heap top tail hv
  · refine ⟨1, ?_⟩
    simpa [ReleasePoint.state, hn, next] using hdispatch'.trans hstep
  · simp only [hn]
    refine ⟨rfl, ?_⟩
    simp [next, hn, hf, cursorTokens, CursorFrame.suffix, flattenPending, hv]


end Compilatrix.Rt.Rc.Procs
