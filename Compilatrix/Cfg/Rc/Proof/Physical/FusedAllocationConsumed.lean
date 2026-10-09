import Compilatrix.Cfg.Rc.Proof.Physical.FusedAllocationInstruction
import Compilatrix.Cfg.Rc.Proof.Native.CtorBinding

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Own Compilatrix.Own.Rc Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix.Rt Compilatrix.Rt.Rc Compilatrix.Rt.Rc.Procs
open Spec

/-- Positive allocation on the actually consumed program. Native admission
supplies all constructor/header/layout constraints and the exact two runtime
procedure lookups; source evaluation supplies the argument multiplicities. -/
theorem fused_allocation_consumed_instruction
    {H : Heap} {external : Nat → Nat} {fields held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external (fields ++ held) live ρf ρo roots)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    (fresh : x ∉ live) (scope : args.all (Own.Plain.argIn live) = true)
    (arguments : Own.evalArgs ρo args = some fields) (positive : 0 < ctor.arity)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem
      (holdRoots external (roots ++ fields ++ held)) context base bump limit slots lists)
    {source : Program} {funcs : List Lir.Func} {main wrapper bound : Nat} {kind : Own.Kind}
    (length : funcs.length = source.base.size)
    (consumed : consume source (layoutOf source) (.bind x (.alloc ctor args kind)) =
      .ok (.bind x (.fir (.call wrapper args))))
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block} {operands : List Lir.Arg}
    (functionLookup : (rawProgram (layoutOf source) funcs main).funcs[caller.fn]? = some function)
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
        Sem.Star (Lir.semStep (rawProgram (layoutOf source) funcs main))
          {mem, ctx := context, stack := caller :: callers} 2
          {mem := finalMem, ctx := context,
            stack := {caller with pos := caller.pos+1, env := caller.env.insert x address, dsts := []} :: callers} ∧
        FusedWords (placeFresh addresses H.size address) (Rt.Proof.Fused lowerTables consumedFunction) bound
          (ρo.insert x allocated.1) (caller.env.insert x address)) ∨
      Sem.Reaches (Lir.semStep (rawProgram (layoutOf source) funcs main))
        {mem, ctx := context, stack := caller :: callers} 2 (.resource .heap)) := by
  obtain ⟨_, nscalar, _, _, argsArity, table, tagBound, _, _, _, small, _⟩ :=
    Spec.consume_allocation positive consumed
  obtain ⟨_, _, _, _, shared⟩ := Spec.table_row table
  obtain ⟨index, call, wrapperLookup, procedureLookup⟩ :=
    Spec.consume_allocation_runtime (main := main) length positive consumed
  have wrapperEq : wrapper = (layoutOf source).allocWrapper index := by
    cases call
    rfl
  have arity : fields.length = ctor.arity := (Own.evalArgs_length ρo arguments).trans argsArity
  have nobj : ctor.nobj = ctor.arity := by simp [Fir.CtorInfo.arity, nscalar]
  rw [← wrapperEq] at wrapperLookup
  exact fused_allocation_instruction before tables ctor args x fresh scope arguments arity positive
    (by omega) tagBound nobj nscalar shared ready wrapperLookup procedureLookup caller callers
    functionLookup blockLookup position statement lowered consumedLookup consumedInstruction related real bounded


end Compilatrix.Cfg.Rc.Native
