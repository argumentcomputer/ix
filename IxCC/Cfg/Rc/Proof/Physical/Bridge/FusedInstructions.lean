import IxCC.Cfg.Rc.Proof.Physical.Bridge.ReadyTokens
import IxCC.Cfg.Rc.Proof.Physical.Bridge.IncrementInstruction
import IxCC.Cfg.Rc.Proof.Physical.Bridge.Instruction
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Native

/-- Actual inc1 instruction for either a live owned value or a borrowed child
whose parent edge proves CanDup. Successful return retains allocator metadata. -/
theorem fused_increment_ready_instruction
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var} {value : RVal}
    (before : Tokens H external held live ρf ρo roots)
    (lookup : ρo.get? x = some value) (permission : CanDup H value)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat} {D : Nat → Prop}
    (wrapperLookup : P.funcs[wrapper]? = some (incrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block}
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (position : caller.pos < block.body.size)
    (statement : block.body[caller.pos] = .call [dummy] wrapper [.v x, .imm 3])
    (registers : FusedWords addresses D bound ρo caller.env)
    (liveOperand : ¬ D x) (reserved : bound ≤ dummy) :
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
          FusedWords addresses D bound ρo (caller.env.insert dummy 1)) ∨
        Sem.Reaches (Lir.semStep P)
          {mem, ctx := context, stack := caller :: callers} 2 (.resource .heap)) := by
  obtain ⟨word, represented, register⟩ := registers.word lookup liveOperand
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
theorem fused_decrement_ready_instruction
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {x : Fir.Var} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held (x :: live) ρf ρo roots)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat} {D : Nat → Prop}
    (wrapperLookup : P.funcs[wrapper]? = some (decrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some dec)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block}
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (position : caller.pos < block.body.size)
    (statement : block.body[caller.pos] = .call [dummy] wrapper [.v x])
    (registers : FusedWords addresses D bound ρo caller.env)
    (liveOperand : ¬ D x) (reserved : bound ≤ dummy) :
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
      FusedWords addresses D bound ρo (caller.env.insert dummy 1) ∧
      (∀ root ∈ held, H.value? root = H'.value? root) := by
  obtain ⟨value, remaining, H', lookup, equal, action, tokens, _, heldValues⟩ := before.decrement
  obtain ⟨word, represented, register⟩ := registers.word lookup liveOperand
  let wrapperEnv : Lir.Env := ({} : Lir.Env).insert 0 word
  let entry : Lir.Frame := {fn := wrapper, label := 0, pos := 0, env := wrapperEnv}
  let suspended : Lir.Frame := {caller with pos := caller.pos+1, dsts := [dummy]}
  have enter : Lir.enter P wrapper [word] = some entry := by
    simp [Lir.enter, wrapperLookup, decrementWrapper, Lir.bindParams, entry, wrapperEnv]
  have args : Lir.evalArgs caller.env [.v x] = some [word] := by
    simp [Lir.evalArgs, Lir.Arg.eval, register]
  have callStep := Lir.step_call (p := P) (mem := mem) (ctx := context)
    (fr := caller) (rest := callers) functionLookup blockLookup position statement args enter
  have argument : wrapperEnv[0]? = some word := Lir.env_insert_self ..
  have rebase : holdRoots external (roots ++ held) =
      fun location => holdRoots external (remaining ++ held) location + refsIn location [value] := by
    funext location
    rw [equal]
    simp only [holdRoots, refsIn_append, refsIn, List.cons_append]
    omega
  have idle := ready.idle
  rw [rebase] at idle
  obtain ⟨physicalHeap, mem', slots', lists', charges, released, restored, trace, protectedBytes⟩ :=
    wrapper_framed idle represented wrapperLookup procedureLookup argument suspended callers rfl
  have physicalAction : Own.Plain.evalAction ρo H (.dec x) = .ok physicalHeap := by
    simp [Own.Plain.evalAction, lookup, released, Sem.Result.ofOption]
  have same : physicalHeap = H' := Sem.Result.ok.inj (physicalAction.symm.trans action)
  subst physicalHeap
  refine ⟨value, remaining, H', mem', slots', lists', charges, lookup, equal,
    action, tokens, ready.after_protected protectedBytes restored, ?_,
    registers.marker reserved 1, heldValues⟩
  have joined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans trace
  simpa only [entry, suspended, Bool.toNat_true, show 1+(1+charges) = 2+charges by omega] using joined



end IxCC.Cfg.Rc.Proof.Physical.Bridge
