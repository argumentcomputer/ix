import Compilatrix.Rt.Rc.Proof.CursorLoads

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

/-- Actual continuation dispatch derives both byte loads and the branch
from the cursor invariant. It reaches block9 exactly when all fields have
been transferred; otherwise it reaches block8. No target clock is charged. -/
theorem ReleaseInvariant.advance_dispatch
    {heap addresses mem external frame tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external none (frame :: tail)
      context base bump limit slots lists)
    (env : Env) (ha : env[8]? = some frame.address) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 6 0) 0
      (releaseState mem context
        ((env.insert 9 (UInt64.ofNat (frame.original.fields.length-frame.visited))).insert 10
          (UInt64.ofNat (smallClass frame.original.fields.length)))
        (if frame.visited = frame.original.fields.length then 9 else 8) 0) := by
  let remaining := UInt64.ofNat (frame.original.fields.length-frame.visited)
  let cls := UInt64.ofNat (smallClass frame.original.fields.length)
  let e1 := env.insert 9 remaining
  let e2 := e1.insert 10 cls
  have hnonzero := h.cursor_nonzero frame (by simp)
  have hloads := h.cursor_loads
  have ha1 : e1[8]? = some frame.address := by
    simp only [e1, Std.HashMap.getElem?_insert]
    change env[8]? = some frame.address
    exact ha
  have hr2 : e2[9]? = some remaining := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]; rfl
  apply Sem.Star.free (s' := releaseState mem context env 7 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, ha, Cond.holds, hnonzero]
  apply Sem.Star.free (s' := releaseState mem context e1 7 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha, hloads.1, remaining, e1]
  apply Sem.Star.free (s' := releaseState mem context e2 7 2)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha1, hloads.2, cls, e2]
  by_cases he : frame.visited = frame.original.fields.length
  · have hz : remaining = 0 := by simp [remaining, he]
    rw [if_pos he]
    apply Sem.Star.free (s' := releaseState mem context e2 9 0)
    · apply semStep_next.mpr
      simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
        takeEdge, bindParams, hr2, hz, Cond.holds, he]
    exact .refl _
  · have hn : remaining ≠ 0 := by
      intro hz
      have hv := h.cursors.2.1.visited_le
      have hs := h.cursors.2.1.small
      have ht := congrArg UInt64.toNat hz
      rw [show remaining.toNat = frame.original.fields.length-frame.visited from
        toNat_ofNat_lt (by omega)] at ht
      change frame.original.fields.length-frame.visited = 0 at ht
      omega
    rw [if_neg he]
    apply Sem.Star.free (s' := releaseState mem context e2 8 0)
    · apply semStep_next.mpr
      simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
        takeEdge, bindParams, hr2, hn, Cond.holds, he]
    exact .refl _


end Compilatrix.Rt.Rc.Procs
