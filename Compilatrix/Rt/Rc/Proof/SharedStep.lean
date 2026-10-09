import Compilatrix.Rt.Rc.Proof.SharedInvariant
import Compilatrix.Rt.Rc.Proof.LiveBranches
import Compilatrix.Rt.Rc.Proof.CountOps
import Compilatrix.Rt.Rc.Proof.CountEncoding

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Proof

/-- Complete shared current-value macro-step. The invariant supplies every
memory access and branch fact; only the cutpoint register correspondence is
an input. The exact source heap and real target memory updates agree. -/
theorem ReleaseInvariant.shared_step
    {heap addresses mem external location frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external (some (.loc location)) frames
      context base bump limit slots lists)
    {rc body address} (hc : heap.cell? location = some (.live (rc+2) .dyn body))
    (ha : addresses location = some address) (env : Env)
    (h1 : env[1]? = some address) (h2 : env[2]? = some (cursorHead frames)) :
    let nextMem := storeCount mem address (UInt64.ofNat rc)
    let nextEnv := ((env.insert 3 (UInt64.ofNat (rc+1))).insert 4 (UInt64.ofNat rc)).insert 8 (cursorHead frames)
    Sem.Star (semStep releaseProgram) (releaseState mem context env 1 0) 0
      (releaseState nextMem context nextEnv 6 0) ∧
    ReleaseInvariant (setCell heap location (.live (rc+1) .dyn body)) addresses nextMem
      external none frames context base bump limit slots lists := by
  obtain ⟨_, a, ham, cell⟩ := h.live.cell location (rc+2) .dyn body hc
  have hae : a = address := by rw [ha] at ham; exact (Option.some.inj ham).symm
  subst a
  let count := UInt64.ofNat (rc+1)
  let e1 := env.insert 3 count
  let e2 := e1.insert 4 (UInt64.ofNat rc)
  let m2 := storeCount mem address (UInt64.ofNat rc)
  have hload : loadWord mem .w32 .zero (address+4) = some count := by simpa [count] using cell.count_load
  have hdyn : Cond.holds .slt .w32 count 0 = false := by simpa [count] using cell.dynamic_branch
  have hshared : Cond.holds .eq .w32 count 0 = false := by simpa [count] using cell.shared_branch (by omega)
  have hcval : count.toNat = (rc+2)-1 := by simpa [count] using cell.count_encoding
  have hnext : X86.Width.w32.truncate (count-1) = UInt64.ofNat rc := by
    apply UInt64.toNat_inj.mp
    rw [shared_decrement_count (by omega : 1 < rc+2) cell.bounded hcval]
    rw [toNat_ofNat_lt (by have := cell.bounded; unfold maxCount at *; omega)]
    omega
  have hr3 : e1[3]? = some count := by simp only [e1, Std.HashMap.getElem?_insert]; rfl
  have hr1 : e2[1]? = some address := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    change env[1]? = some address
    exact h1
  have hr2 : e2[2]? = some (cursorHead frames) := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    change env[2]? = some (cursorHead frames)
    exact h2
  have hr4 : e2[4]? = some (UInt64.ofNat rc) := by simp only [e2, Std.HashMap.getElem?_insert]; rfl
  refine ⟨?_, h.shared_complete hc ha⟩
  apply Sem.Star.free (s' := releaseState mem context env 2 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, h1, cell.pointer_branch]
  apply Sem.Star.free (s' := releaseState mem context e1 2 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, h1, hload, e1]
  apply Sem.Star.free (s' := releaseState mem context e1 3 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hr3, hdyn]
  apply Sem.Star.free (s' := releaseState mem context e1 4 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hr3, hshared]
  apply Sem.Star.free (s' := releaseState mem context e2 4 1)
  · apply semStep_next.mpr
    simpa only [releaseProgram, releaseState, e2, hnext] using dec_sub_step mem context count e1 hr3
  apply Sem.Star.free (s' := releaseState m2 context e2 4 2)
  · apply semStep_next.mpr
    exact dec_store_step mem context address (UInt64.ofNat rc) e2 hr1 hr4 cell.count_writable
  apply Sem.Star.free (s' := releaseState m2 context (e2.insert 8 (cursorHead frames)) 6 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hr2]
  exact .refl _


end Compilatrix.Rt.Rc.Procs
