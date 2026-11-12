import IxCC.Rt.Rc.Gen.Proof.LiveBranches
import IxCC.Rt.Rc.Gen.Proof.Detach

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

/-- Unique dispatch reads the actual count from a represented live cell.
The sole remaining register premise is the current cutpoint pointer. -/
theorem LiveCell.unique_dispatch {addresses mem address body}
    (cell : LiveCell addresses mem address 1 body) (context : Word) (env : Env)
    (h1 : env[1]? = some address) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 1 0) 0
      (releaseState mem context (env.insert 3 0) 5 0) := by
  let e1 := env.insert 3 0
  have hload : loadWord mem .w32 .zero (address+4) = some 0 := by
    simpa using cell.count_load
  have hdyn : Cond.holds .slt .w32 0 0 = false := by simpa using cell.dynamic_branch
  have hr3 : e1[3]? = some 0 := by simp only [e1, Std.HashMap.getElem?_insert]; rfl
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
  apply Sem.Star.free (s' := releaseState mem context e1 5 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hr3, Cond.holds]
  exact .refl _


end IxCC.Rt.Rc.Gen
