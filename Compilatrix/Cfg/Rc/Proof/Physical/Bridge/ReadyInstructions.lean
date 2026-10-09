import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ReadyTokens
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.IncrementInstruction
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Instruction

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs Compilatrix.Cfg.Rc.Native

/-- Actual inc1 instruction for either a live owned value or a borrowed child
whose parent edge proves CanDup. Successful return retains allocator metadata. -/
theorem increment_ready_instruction
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var} {value : RVal}
    (before : Tokens H external held live ρf ρo roots)
    (lookup : ρo.get? x = some value) (permission : CanDup H value)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (incrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block}
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (position : caller.pos < block.body.size)
    (statement : block.body[caller.pos] = .call [dummy] wrapper [.v x, .imm 3])
    (registers : EnvWordsBelow addresses bound ρo caller.env)
    (real : x < bound) (reserved : bound ≤ dummy) :
    ∃ H', Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external (value :: held) live ρf ρo roots ∧
      (∀ root, H.value? root = H'.value? root) ∧
      ((∃ mem', AllocatorReady H' addresses mem'
          (holdRoots external (roots ++ value :: held))
          context base bump limit slots lists ∧
          Sem.Star (Lir.semStep P)
            {mem, ctx := context, stack := caller :: callers} 2
            {mem := mem', ctx := context,
              stack := {caller with
                pos := caller.pos+1
                env := caller.env.insert dummy 1
                dsts := []} :: callers} ∧
          EnvWordsBelow addresses bound ρo (caller.env.insert dummy 1)) ∨
        Sem.Reaches (Lir.semStep P)
          {mem, ctx := context, stack := caller :: callers} 2 (.resource .heap)) := by
  obtain ⟨word, represented, register⟩ := registers x value real lookup
  let wrapperEnv : Lir.Env := (({} : Lir.Env).insert 0 word).insert 1 3
  let entry : Lir.Frame := {fn := wrapper, label := 0, pos := 0, env := wrapperEnv}
  let suspended : Lir.Frame := {caller with pos := caller.pos+1, dsts := [dummy]}
  have enter : Lir.enter P wrapper [word, 3] = some entry := by
    simp [Lir.enter, wrapperLookup, incrementWrapper, Lir.bindParams, entry, wrapperEnv]
  have args : Lir.evalArgs caller.env [.v x, .imm 3] = some [word, 3] := by
    simp [Lir.evalArgs, Lir.Arg.eval, register]
  have callStep := Lir.step_call (p := P) (mem := mem) (ctx := context)
    (fr := caller) (rest := callers) functionLookup blockLookup position statement args enter
  have argument : wrapperEnv[0]? = some word := by
    change ((({} : Lir.Env).insert 0 word).insert 1 3)[0]? = some word
    rw [Lir.env_insert_ne _ _ (by decide : (1 : Nat) ≠ 0), Lir.env_insert_self]
  obtain ⟨H', action, tokens, values, outcome⟩ :=
    increment_ready_tokens before lookup permission ready represented
  refine ⟨H', action, tokens, values, ?_⟩
  rcases outcome with ⟨mem', restored, result⟩ | failure
  · have trace := increment_wrapper_success wrapperLookup procedureLookup argument
      suspended callers (dummy := dummy) rfl result
    refine .inl ⟨mem', restored, ?_, registers.marker reserved 1⟩
    have joined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans trace
    simpa only [entry, suspended, Bool.toNat_true] using joined
  · have failed := increment_wrapper_failure wrapperLookup procedureLookup argument
      (suspended :: callers) failure
    have joined := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr callStep)) failed
    exact .inr (by simpa only [entry, suspended, Bool.toNat_true] using joined)

/-- Upgrade the validated decrement instruction with its proved memory frame.
The resulting invariant can immediately feed another allocation. -/
theorem decrement_ready_instruction
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {x : Fir.Var} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held (x :: live) ρf ρo roots)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
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
      AllocatorReady H' addresses mem' (holdRoots external (remaining ++ held))
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := caller :: callers} (2 + charges)
        {mem := mem', ctx := context,
          stack := {caller with
            pos := caller.pos+1
            env := caller.env.insert dummy 1
            dsts := []} :: callers} ∧
      EnvWordsBelow addresses bound ρo (caller.env.insert dummy 1) ∧
      (∀ root ∈ held, H.value? root = H'.value? root) := by
  obtain ⟨value, remaining, H', mem', slots', lists', charges, lookup, equal,
    action, tokens, idle, trace, frame, represented, values⟩ :=
    decrement_instruction before ready.idle wrapperLookup procedureLookup caller callers
      functionLookup blockLookup position statement registers real reserved
  exact ⟨value, remaining, H', mem', slots', lists', charges, lookup, equal,
    action, tokens, ready.after_protected frame idle, trace, represented, values⟩



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
