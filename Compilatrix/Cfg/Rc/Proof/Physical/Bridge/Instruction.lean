import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Cursor

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Cfg.Rc.Native

/-- Execute the actual caller statement, not an assumed call step. The
concrete statement and function lookups are supplied by raw accepted layout;
all ownership effects and the complete release trace are constructed here. -/
theorem decrement_instruction
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {x : Fir.Var} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held (x :: live) ρf ρo roots)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (idle : ReleaseInvariant H addresses mem (holdRoots external (roots ++ held)) none []
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (decrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some dec)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block}
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (position : caller.pos < block.body.size)
    (statement : block.body[caller.pos] = .call [dummy] wrapper [.v x])
    (registers : EnvWordsBelow addresses bound ρo caller.env)
    (real : x < bound) (reserved : bound ≤ dummy) :
    ∃ value remaining H' mem' slots' lists' charges,
      ρo.get? x = some value ∧ roots = value :: remaining ∧
      Own.Plain.evalAction ρo H (.dec x) = .ok H' ∧
      Tokens H' external held live ρf ρo remaining ∧
      ReleaseInvariant H' addresses mem' (holdRoots external (remaining ++ held)) none []
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := caller :: callers}
        (2 + charges)
        {mem := mem', ctx := context,
          stack := {caller with
            pos := caller.pos+1
            env := caller.env.insert dummy 1
            dsts := []} :: callers} ∧
      ProtectedFrame mem mem' context base bump ∧
      EnvWordsBelow addresses bound ρo (caller.env.insert dummy 1) ∧
      (∀ root ∈ held, H.value? root = H'.value? root) := by
  obtain ⟨value, remaining, lookup, _, _⟩ := Own.Plain.envRoots_cons before.exactRoots
  obtain ⟨word, _, register⟩ := registers x value real lookup
  let wrapperEnv : Lir.Env := ({} : Lir.Env).insert 0 word
  let entry : Lir.Frame := {fn := wrapper, label := 0, pos := 0, env := wrapperEnv}
  let suspended : Lir.Frame := {caller with pos := caller.pos+1, dsts := [dummy]}
  have enter : Lir.enter P wrapper [word] = some entry := by
    simp [Lir.enter, wrapperLookup, decrementWrapper, Lir.bindParams, entry, wrapperEnv]
  have args : Lir.evalArgs caller.env [.v x] = some [word] := by
    simp [Lir.evalArgs, Lir.Arg.eval, register]
  have callStep := Lir.step_call (p := P) (mem := mem) (ctx := context)
    (fr := caller) (rest := callers) functionLookup blockLookup position statement args enter
  have argument : wrapperEnv[0]? = suspended.env[x]? := by
    simpa [wrapperEnv, suspended] using register.symm
  obtain ⟨value', remaining', H', mem', slots', lists', charges, lookup', equal,
    action, tokens, restored, trace, protectedBytes, represented, heldValues⟩ :=
    decrement_wrapper_tokens before idle wrapperLookup procedureLookup suspended callers
      registers real reserved argument rfl
  refine ⟨value', remaining', H', mem', slots', lists', charges, lookup', equal,
    action, tokens, restored, ?_, protectedBytes, represented, heldValues⟩
  have joined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans trace
  simpa only [entry, suspended, Bool.toNat_true, show 1+(1+charges) = 2+charges by omega] using joined


end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
