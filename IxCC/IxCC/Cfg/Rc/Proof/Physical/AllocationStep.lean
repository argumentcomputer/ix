import IxCC.Cfg.Rc.Proof.Physical.FusedAllocationConsumed
import IxCC.Cfg.Rc.Proof.Physical.ConsumedMarkers

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Execute the positive allocation at an actual source cursor. Admission
and lowering provide every constructor/runtime lookup and the caller's
statement. Both operand overflow and exhausted allocation are actual finite
resource executions, with no successful-lowering or space premise. -/
theorem allocation_step
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    {kind : Own.Kind} {tail : List Cfg.Instr}
    (head : source.rest = .bind x (.alloc ctor args kind) :: tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {fields held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external (fields ++ held) live ρf ρo roots)
    (fresh : x ∉ live) (scope : args.all (Own.Plain.argIn live) = true)
    (arguments : Own.evalArgs ρo args = some fields) (positive : 0 < ctor.arity)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ (fields ++ held)))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (real : x < bound) (bounded : Own.Plain.EnvBounded H.size ρo)
    (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ logical address next mem' slots' lists',
      Fir.evalArgs ρf args = some logical ∧
      let allocated := H.alloc .rc {ctor, fields}
      Own.Plain.evalRhs tables ρo H (.ctor ctor args) = .ok allocated ∧
      Tokens allocated.2 external held (live ++ [x])
        (ρf.insert x (.ctor ctor logical)) (ρo.insert x allocated.1) (roots ++ [allocated.1]) ∧
      AllocatorReady allocated.2 (placeFresh addresses H.size address) mem'
        (holdRoots external ((roots ++ [allocated.1]) ++ held))
        context base next limit slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} 2
        {mem := mem', ctx := context,
          stack := {target with pos := target.pos+1, env := target.env.insert x address, dsts := []} :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main)
        {source with rest := tail, env := source.env.insert x allocated.1}
        {target with pos := target.pos+1, env := target.env.insert x address, dsts := []} ∧
      FusedWords (placeFresh addresses H.size address)
        (Rt.Proof.Fused (tablesOf P pairs) function) bound
        (ρo.insert x allocated.1) (target.env.insert x address)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨actual, rest, consuming, _, position⟩ := cursor.next head
  obtain ⟨index, result, wrapperLookup, procedureLookup⟩ :=
    consume_allocation_runtime (funcs := (List.range P.base.size).map functions)
      (main := main) (by simp) positive consuming
  subst actual
  obtain ⟨_, nscalar, _, _, argsArity, table, tagBound, _, _, _, small, _⟩ :=
    consume_allocation positive consuming
  obtain ⟨_, _, _, _, shared⟩ := table_row table
  have arity : fields.length = ctor.arity := (Own.evalArgs_length ρo arguments).trans argsArity
  have nobj : ctor.nobj = ctor.arity := by simp [Fir.CtorInfo.arity, nscalar]
  obtain ⟨fd, block, _, _, _, _, _, _, lookup, blockLookup,
    _, _, _, _, _, _, _, _, _, ⟨pre, body⟩, fn, _, _⟩ := position
  rw [sourceLookup] at lookup
  cases lookup
  have member : Cfg.Instr.bind x (.fir (.call ((layoutOf P).allocWrapper index) args)) ∈
      block.body := by
    rw [← body]
    simp
  rcases cursor.call head consuming mem context callers with success | failure
  · obtain ⟨operands, nativeFunction, nativeBlock, lowered, nativeLookup, nativeBlockLookup,
      nativePosition, statement, continuation⟩ := success
    have lowered' : Rt.Lower.operands target.fn args = .ok (some operands) := by
      simpa only [fn] using lowered
    obtain ⟨logical, sourceArgs, effect, tokens, outcome⟩ :=
      fused_allocation_instruction before tables ctor args x fresh scope arguments arity positive
        (by omega) tagBound nobj nscalar shared (by simpa only [List.append_assoc] using ready)
        (raw_public_runtime wrapperLookup) (raw_public_runtime procedureLookup) target callers
        nativeLookup nativeBlockLookup nativePosition statement lowered' blockLookup member registers real bounded
    rcases outcome with ⟨address, next, mem', slots', lists', restored, trace, words⟩ | failed
    · exact .inl ⟨logical, address, next, mem', slots', lists', sourceArgs, effect, tokens,
        restored, trace, continuation.withEnvs (source.env.insert x (H.alloc .rc {ctor, fields}).1)
          (target.env.insert x address) [], words⟩
    · exact .inr (reaches_resource_fails failed)
  · right
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        ({mem, ctx := context, stack := target :: callers} : Lir.State) := by
      cases target
      simp_all [Lir.atState]
    rw [same] at failure
    exact failure


end IxCC.Cfg.Rc.Native
