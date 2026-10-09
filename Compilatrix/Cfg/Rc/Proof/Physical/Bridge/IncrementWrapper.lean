import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.IncrementTokens
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FailureTransport
import Compilatrix.Cfg.Rc.Proof.Physical.IncWrapper

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs Compilatrix.Cfg.Rc.Native

theorem increment_wrapper_success
    {P : Lir.Program} {wrapper procedure dummy : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (incrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    {mem after : X86.Memory} {context word : Lir.Word} {env : Lir.Env}
    (argument : env[0]? = some word)
    (caller : Lir.Frame) (callers : List Lir.Frame) (destination : caller.dsts = [dummy])
    (result : Lir.eval incProgram 0 [word] mem context = .ok ([], after)) :
    Sem.Star (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
      {mem := after, ctx := context,
        stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: callers} := by
  let continuation : Lir.Frame := {fn := wrapper, label := 0, pos := 1, env, dsts := []}
  have enter : Lir.enter P procedure [word] =
      some {fn := procedure, label := 0, pos := 0, env := incEnv word} := by
    simp [Lir.enter, procedureLookup, Rt.Rc.Procs.inc, Lir.bindParams, incEnv]
  have callStep := increment_wrapper_call (env := env) (rest := caller :: callers)
    (mem := mem) (ctx := context) wrapperLookup argument enter
  have localRun := (Lir.runs_eval (inc_initial mem context word)) 0
  dsimp only at localRun
  rw [result] at localRun
  let frame : Lir.Frame := {fn := 0, label := 0, pos := 0, env := incEnv word}
  have localTrace : Sem.Reaches (Lir.semStep (localProgram Rt.Rc.Procs.inc))
      (localState mem context frame) 0 (.ok ([], after)) := by
    simpa only [localProgram, incProgram, localState, incState, frame] using localRun
  obtain ⟨charges, bounded, trace⟩ := local_success_transport Rt.Rc.Procs.inc inc_call_free P procedure
    procedureLookup mem context frame rfl continuation (caller :: callers)
      (env := env) localTrace (by simp [continuation, Lir.bindParams])
  have zero : charges = 0 := by omega
  subst charges
  have returnStep := marker_return (callee := procedure) (env := env) (caller := caller)
    (rest := callers) (mem := after) (ctx := context) wrapperLookup rfl destination
  have joined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans
    (trace.trans (Sem.Star.single (Lir.semStep_next.mpr returnStep)))
  simpa [frame, continuation, ambientState] using joined

theorem increment_wrapper_failure
    {P : Lir.Program} {wrapper procedure : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (incrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    {mem : X86.Memory} {context word : Lir.Word} {env : Lir.Env}
    (argument : env[0]? = some word) (callers : List Lir.Frame)
    (result : Lir.eval incProgram 0 [word] mem context = .resource .heap) :
    Sem.Reaches (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: callers}
      1 (.resource .heap) := by
  let continuation : Lir.Frame := {fn := wrapper, label := 0, pos := 1, env, dsts := []}
  have enter : Lir.enter P procedure [word] =
      some {fn := procedure, label := 0, pos := 0, env := incEnv word} := by
    simp [Lir.enter, procedureLookup, Rt.Rc.Procs.inc, Lir.bindParams, incEnv]
  have callStep := increment_wrapper_call (env := env) (rest := callers)
    (mem := mem) (ctx := context) wrapperLookup argument enter
  have localRun := (Lir.runs_eval (inc_initial mem context word)) 0
  dsimp only at localRun
  rw [result] at localRun
  let frame : Lir.Frame := {fn := 0, label := 0, pos := 0, env := incEnv word}
  have localTrace : Sem.Reaches (Lir.semStep (localProgram Rt.Rc.Procs.inc))
      (localState mem context frame) 0 (.resource .heap) := by
    simpa only [localProgram, incProgram, localState, incState, frame] using localRun
  have failed := local_resource_transport Rt.Rc.Procs.inc inc_call_free P procedure procedureLookup
    mem context frame rfl (continuation :: callers) localTrace
  have joined := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr callStep)) failed
  simpa [frame, continuation, ambientState] using joined

/-- Complete inc1 wrapper branch: either the actual count update returns, or
the actual maximal-count branch fails with resource.heap. There is no room
premise. The newly produced ownership occurrence is carried separately from
the distinct lexical live-variable roots. -/
theorem increment_wrapper_tokens
    {H : Heap} {external : Nat → Nat} {held carry roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var}
    (before : Tokens H external (carry ++ held) live ρf ρo roots) (member : x ∈ live)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (idle : ReleaseInvariant H addresses mem (holdRoots external (roots ++ carry ++ held)) none []
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat} {env : Lir.Env}
    (wrapperLookup : P.funcs[wrapper]? = some (incrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    (registers : EnvWordsBelow addresses bound ρo caller.env)
    (real : x < bound) (reserved : bound ≤ dummy)
    (argument : env[0]? = caller.env[x]?) (destination : caller.dsts = [dummy]) :
    ∃ value H', ρo.get? x = some value ∧
      Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external ((value :: carry) ++ held) live ρf ρo roots ∧
      ((∃ mem', ReleaseInvariant H' addresses mem'
          (holdRoots external (roots ++ (value :: carry) ++ held)) none []
          context base bump limit slots lists ∧
          Sem.Star (Lir.semStep P)
            {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
            {mem := mem', ctx := context,
              stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: callers} ∧
          EnvWordsBelow addresses bound ρo (caller.env.insert dummy 1)) ∨
        Sem.Reaches (Lir.semStep P)
          {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
          1 (.resource .heap)) := by
  obtain ⟨value, logical, lookup, _, _⟩ := before.den x member
  obtain ⟨word, represented, register⟩ := registers x value real lookup
  obtain ⟨H', action, tokens, _, outcome⟩ := increment_entry_tokens before member lookup idle represented
  refine ⟨value, H', lookup, action, tokens, ?_⟩
  rcases outcome with ⟨mem', restored, result⟩ | failure
  · exact .inl ⟨mem', restored, increment_wrapper_success wrapperLookup procedureLookup
      (argument.trans register) caller callers destination result, registers.marker reserved 1⟩
  · exact .inr (increment_wrapper_failure wrapperLookup procedureLookup
      (argument.trans register) (caller :: callers) failure)




end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
