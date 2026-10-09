import Compilatrix.Cfg.Rc.Proof.Physical.AllocSteps
import Compilatrix.Cfg.Rc.Proof.Physical.AllocCaller
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FailureTransport
import Compilatrix.Rt.Rc.Proof.AllocFailure

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Lir
open Compilatrix.Rt Compilatrix.Rt.Rc Compilatrix.Rt.Rc.Procs

theorem allocation_wrapper_failure {fields tag : Nat}
    (positive : 0 < fields) (small : fields < 32) (tagBound : tag ≤ maxTag)
    {mem : X86.Memory} {context : Word}
    (failure : Lir.eval (allocProgram fields tag) 0 [] mem context = .resource .heap)
    {P : Lir.Program} {wrapper procedure : Nat} {env : Lir.Env}
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure fields))
    (procedureLookup : P.funcs[procedure]? = some (alloc fields tag)) (callers : List Lir.Frame) :
    Sem.Reaches (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: callers}
      1 (.resource .heap) := by
  have enter : Lir.enter P procedure [] = some {fn := procedure, label := 0, pos := 0, env := {}} := by
    simp [Lir.enter, procedureLookup, alloc, Nat.ne_of_gt positive,
      Nat.not_le.mpr small, Nat.not_lt.mpr tagBound, Lir.bindParams]
  have callStep := allocation_call (env := env) (rest := callers)
    (mem := mem) (ctx := context) wrapperLookup enter
  let continuation : Lir.Frame := {fn := wrapper, label := 0, pos := 1, env, dsts := [fields]}
  let frame : Lir.Frame := {fn := 0, label := 0, pos := 0, env := {}}
  have reaches := (Lir.runs_eval (alloc_free_initial mem context fields tag positive small tagBound)) 0
  dsimp only at reaches
  rw [failure] at reaches
  have localRun : Sem.Reaches (Lir.semStep (localProgram (alloc fields tag)))
      (localState mem context frame) 0 (.resource .heap) := by
    simpa only [localProgram, allocProgram, localState, allocState, frame] using reaches
  have failed := Compilatrix.Cfg.Rc.Proof.Physical.Bridge.local_resource_transport (alloc fields tag) (allocator_call_free fields tag)
    P procedure procedureLookup mem context frame rfl (continuation :: callers) localRun
  have joined := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr callStep)) failed
  simpa [frame, continuation, ambientState] using joined

/-- Empty class plus insufficient bounded storage follows actual heap failure;
no space premise or successful operation is silently required by the wrapper. -/
theorem allocation_short_failure {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields tag : Nat} (positive : 0 < fields) (small : fields < 32) (tagBound : tag ≤ maxTag)
    (empty : lists (smallClass fields) = []) (short : limit.toNat < bump.toNat + cellBytes fields)
    {P : Lir.Program} {wrapper procedure : Nat} {env : Lir.Env}
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure fields))
    (procedureLookup : P.funcs[procedure]? = some (alloc fields tag)) (callers : List Lir.Frame) :
    Sem.Reaches (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: callers}
      1 (.resource .heap) :=
  allocation_wrapper_failure positive small tagBound
    (ready.reserve_short positive small tagBound empty short 0) wrapperLookup procedureLookup callers



end Compilatrix.Cfg.Rc.Native
