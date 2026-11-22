import IxCC.Rt.Rc.Proof.IncrementCases
import IxCC.Rt.Rc.Proof.SuccessTransport

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

theorem inc_call_free : CallFree inc := by
  simp [CallFree, inc]

theorem increment_caller_complete
    {heap addresses mem external context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {location refs body address} (hc : heap.cell? location = some (.live refs .dyn body))
    (ha : addresses location = some address) (hroom : refs < maxCount)
    (P : Program) (fn : Nat) (hfn : P.funcs[fn]? = some inc)
    (caller : Frame) (callers : List Frame) (hdsts : caller.dsts = []) :
    Own.Rc.inc heap (.loc location) 1 = some (setCell heap location (.live (refs+1) .dyn body)) ∧
    ReleaseInvariant (setCell heap location (.live (refs+1) .dyn body)) addresses
      (storeCount mem address (UInt64.ofNat refs))
      (fun k => external k + refsIn k [.loc location]) none [] context base bump limit slots lists ∧
    Sem.Star (semStep P)
      { mem, ctx := context, stack := { fn, label := 0, pos := 0, env := incEnv address } :: caller :: callers }
      0 { mem := storeCount mem address (UInt64.ofNat refs), ctx := context, stack := caller :: callers } := by
  obtain ⟨hs, hi, heval⟩ := increment_entry_complete h hc ha hroom
  have hrun := (runs_eval (inc_initial mem context address)) 0
  dsimp only at hrun
  rw [heval] at hrun
  let frame : Frame := { fn := 0, label := 0, pos := 0, env := incEnv address }
  have hlocal : Sem.Reaches (semStep (localProgram inc)) (localState mem context frame) 0
      (.ok ([], storeCount mem address (UInt64.ofNat refs))) := by
    simpa only [localProgram, incProgram, localState, incState, frame] using hrun
  obtain ⟨charges, hle, hsteps⟩ := local_success_transport inc inc_call_free P fn hfn mem context frame
    rfl caller callers (env := caller.env) hlocal (by simp [hdsts, bindParams])
  have hz : charges = 0 := by omega
  subst charges
  refine ⟨hs, hi, ?_⟩
  have he : {caller with env := caller.env, dsts := []} = caller := by
    cases caller with
    | mk f l p e ds =>
      change ds = [] at hdsts
      subst ds
      rfl
  simpa only [ambientState, frame, he] using hsteps



end IxCC.Rt.Rc.Procs
