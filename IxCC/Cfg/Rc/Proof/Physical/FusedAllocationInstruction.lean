import IxCC.Cfg.Rc.Proof.Physical.FusedAllocationSource
import IxCC.Cfg.Rc.Proof.Physical.AllocationArguments
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Own IxCC.Own.Rc IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- Execute a real lowered positive-constructor call, starting in its source
caller. Operand words and wrapper parameter registers are derived internally;
the two charged calls either restore the source caller with the new owned
root and complete arena invariant, or reach actual heap exhaustion. -/
theorem fused_allocation_instruction
    {H : Heap} {external : Nat → Nat} {fields held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external (fields ++ held) live ρf ρo roots)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    (fresh : x ∉ live) (scope : args.all (Own.Plain.argIn live) = true)
    (arguments : Own.evalArgs ρo args = some fields) (arity : fields.length = ctor.arity)
    (positive : 0 < ctor.arity) (small : ctor.arity < 32)
    (tagBound : ctor.tag ≤ maxTag) (nobj : ctor.nobj = ctor.arity)
    (nscalar : ctor.nscalar = 0) (shared : ctor.fieldKinds = List.replicate ctor.arity .shared)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem
      (holdRoots external (roots ++ fields ++ held)) context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure bound : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure ctor.arity))
    (procedureLookup : P.funcs[procedure]? = some (alloc ctor.arity ctor.tag))
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block} {operands : List Lir.Arg}
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (position : caller.pos < block.body.size)
    (statement : block.body[caller.pos] = .call [x] wrapper operands)
    (lowered : Lower.operands caller.fn args = .ok (some operands))
    {lowerTables : Lower.Tables} {consumedFunction : Cfg.Fun}
    {consumedIndex : Nat} {consumedBlock : Cfg.Block}
    (consumedLookup : consumedFunction.blocks[consumedIndex]? = some consumedBlock)
    (consumedInstruction : Cfg.Instr.bind x (.fir (.call wrapper args)) ∈ consumedBlock.body)
    (related : FusedWords addresses (Rt.Proof.Fused lowerTables consumedFunction) bound ρo caller.env)
    (real : x < bound)
    (bounded : Own.Plain.EnvBounded H.size ρo) :
    ∃ sourceValues,
      Fir.evalArgs ρf args = some sourceValues ∧
      let allocated := H.alloc .rc {ctor, fields}
      Own.Plain.evalRhs tables ρo H (.ctor ctor args) = .ok allocated ∧
      Tokens allocated.2 external held (live ++ [x])
        (ρf.insert x (.ctor ctor sourceValues)) (ρo.insert x allocated.1) (roots ++ [allocated.1]) ∧
      ((∃ address next finalMem finalSlots finalLists,
        AllocatorReady allocated.2 (placeFresh addresses H.size address) finalMem
          (holdRoots external ((roots ++ [allocated.1]) ++ held))
          context base next limit finalSlots finalLists ∧
        Sem.Star (Lir.semStep P)
          {mem, ctx := context, stack := caller :: callers} 2
          {mem := finalMem, ctx := context,
            stack := {caller with pos := caller.pos+1, env := caller.env.insert x address, dsts := []} :: callers} ∧
        FusedWords (placeFresh addresses H.size address) (Rt.Proof.Fused lowerTables consumedFunction) bound
          (ρo.insert x allocated.1) (caller.env.insert x address)) ∨
      Sem.Reaches (Lir.semStep P)
        {mem, ctx := context, stack := caller :: callers} 2 (.resource .heap)) := by
  obtain ⟨words, wordArgs, wordValues, _⟩ :=
    fused_call_operands_words related consumedLookup consumedInstruction lowered arguments
  obtain ⟨env, binding, registers, values⟩ := allocation_bind_arguments wordValues
  let entry : Lir.Frame := {fn := wrapper, label := 0, pos := 0, env}
  let suspended : Lir.Frame := {caller with pos := caller.pos+1, dsts := [x]}
  have enter : Lir.enter P wrapper words = some entry := by
    simp [Lir.enter, wrapperLookup, allocationWrapper, ← arity, binding, entry]
  have callStep := Lir.step_call (p := P) (mem := mem) (ctx := context)
    (fr := caller) (rest := callers) functionLookup blockLookup position statement wordArgs enter
  obtain ⟨sourceValues, sourceArgs, effect, tokens, outcome⟩ :=
    fused_allocation_source_wrapper before tables ctor args x fresh scope arguments arity positive small
      tagBound nobj nscalar shared ready (fun i => words[i]?.getD 0)
      wrapperLookup procedureLookup registers values suspended callers rfl related real bounded
  refine ⟨sourceValues, sourceArgs, effect, tokens, ?_⟩
  rcases outcome with ⟨address, next, finalMem, finalSlots, finalLists, restored, trace, represented⟩ | failure
  · refine .inl ⟨address, next, finalMem, finalSlots, finalLists, restored, ?_, represented⟩
    have joined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans trace
    simpa only [entry, suspended, Bool.toNat_true] using joined
  · have joined := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr callStep)) failure
    exact .inr (by simpa only [entry, suspended, Bool.toNat_true] using joined)


end IxCC.Cfg.Rc.Native
