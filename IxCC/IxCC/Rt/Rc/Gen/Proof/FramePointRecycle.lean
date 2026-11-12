import IxCC.Rt.Rc.Gen.Proof.ProtectedOps
import IxCC.Rt.Rc.Gen.Proof.ReleasePoint
import IxCC.Rt.Rc.Gen.Proof.RecycleDetailed
import IxCC.Rt.Rc.Gen.Proof.AdvanceDispatch

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ReleasePoint.recycle_move_frame {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid cmax addresses external context base bump limit) {top tail}
    (hn : p.current = none) (hf : p.frames = top :: tail)
    (hv : top.visited = top.original.ctor.nobj) :
    ∃ next, p.Move cmax addresses external context base bump limit next ∧
      ProtectedFrame p.mem next.mem context base bump := by
  obtain ⟨hi, hr⟩ := hp
  have hi' : ReleaseInvariant cmax p.heap addresses p.mem external none (top :: tail)
      context base bump limit p.slots p.lists := by simpa only [hn, hf] using hi
  have hr' : p.env[8]? = some top.address := by simpa only [hn, hf, cursorHead] using hr
  let cls := UInt64.ofNat (classOf top.original.ctor)
  let remaining := UInt64.ofNat (top.original.ctor.nobj-top.visited)
  let env := (p.env.insert 9 remaining).insert 10 (UInt64.ofNat top.original.ctor.nobj)
  have h8 : env[8]? = some top.address := by
    simp only [env, Std.HashMap.getElem?_insert]
    exact hr'
  have hdispatch := hi'.advance_dispatch p.env hr'
  have hdispatch' : Sem.Star (semStep releaseProgram) (releaseState p.mem context p.env 6 0) 0
      (releaseState p.mem context env 9 0) := by
    simpa only [hv, ↓reduceIte, env, remaining] using hdispatch
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
    have := hi'.cursor_bytes (frame := top) (by simp)
    omega
  have hstep := finished_parent_recycle p.mem context (UInt64.ofNat parent.cls) parent.address
    (cursorHead tail) ((p.lists parent.cls).headD 0) env (by simpa only [ha] using h8)
    (by simpa only [ha, hc] using hi'.cursor_loads.2.2) hpred hload hwrite
    (hi'.head_writable parent.cls vp.1 vp.2.1)
  let next : ReleasePoint := {p with
    mem := recycleParent p.mem context (UInt64.ofNat parent.cls) parent.address ((p.lists parent.cls).headD 0)
    frames := tail
    slots := recycleSlots parent.address p.slots
    lists := pushFree p.lists parent.cls parent.address
    env := ((((env.insert 11 (UInt64.ofNat parent.cls)).insert 15 (cursorHead tail)).insert 16 ((p.lists parent.cls).headD 0)).insert 8 (cursorHead tail))}
  refine ⟨next, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [next, hn] using hiNext
    · simp only [next, hn, Std.HashMap.getElem?_insert]; rfl
  · simpa only [ReleasePoint.rank, next, hn, hf] using cutpoint_pop_decreases p.heap top tail
  · refine ⟨1, ?_⟩
    have hs := hdispatch'.trans hstep
    simpa only [ReleasePoint.state, hn, next, Option.isSome_none, Bool.false_eq_true, ite_false,
      Nat.zero_add] using hs
  · refine ⟨top.suffix, hi'.cursors.2.1.suffix_scalars hv, ?_⟩
    simp only [hn]
    refine ⟨rfl, ?_⟩
    simp [next, hf, cursorTokens, flattenPending]
    exact hn

  · exact hi'.recycle_protected hm ((p.lists parent.cls).headD 0)


end IxCC.Rt.Rc.Gen
