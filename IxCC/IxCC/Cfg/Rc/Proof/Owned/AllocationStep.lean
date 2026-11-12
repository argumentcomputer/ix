import IxCC.Cfg.Rc.Proof.Native.CtorBinding
import IxCC.Cfg.Rc.Proof.Physical.ConsumedMarkers
import IxCC.Cfg.Rc.Proof.Physical.AllocationArguments
import IxCC.Cfg.Rc.Proof.Physical.AllocationOutcome
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords
import IxCC.Own.Plain.Proof.Actions

/-! # The allocation step for a multiset of tokens (heap stage 2)

`allocation_step` (and the two lemmas under it) take the arguments' tokens from `Tokens` over a
lexical list in which every argument variable occurs exactly once. Under the ownership checker's
typing context the arguments' tokens are taken from a multiset (`takeArgs`), and no such list
exists. The variants here take instead what the step needs: the fields' values (`Own.evalArgs`),
their source values with denotation, and the fields' reference counts held apart from the other
tokens (`Balance H (holdRoots external held) fields`). The physical part is unchanged
(`allocation_outcome`). -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc.Procs

/-- `fused_allocation_source_wrapper` with the fields' tokens given directly. -/
theorem fused_allocation_source_wrapper_of
    {H : Heap} {external : Nat → Nat} {fields held : List RVal} {ρo : Own.Env}
    {logical : List Fir.Val}
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    (arguments : Own.evalArgs ρo args = some fields)
    (den : Sem.Forall2 (Own.Proof.Den H) fields logical)
    (balance : Balance H (holdRoots external held) fields)
    (arity : fields.length = ctor.arity)
    (positive : 0 < ctor.arity) (small : ctor.arity ≤ maxFields)
    (tagBound : ctor.tag ≤ maxTag) (nobj : ctor.nobj = ctor.arity)
    (nscalar : ctor.nscalar = 0) (shared : ctor.fieldKinds = List.replicate ctor.arity .shared)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (holdRoots external (fields ++ held)) context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure bound : Nat} {env : Lir.Env}
    (words : Nat → Lir.Word)
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure ctor.arity))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields ctor.arity ctor.tag)))
    (registers : ∀ i < fields.length, env[i]? = some (words i))
    (values : ∀ j value, fields[j]? = some value → valueWord addresses value = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [x])
    {D : Nat → Prop} (related : FusedWords addresses D bound ρo caller.env)
    (real : x < bound)
    (bounded : Own.Plain.EnvBounded H.size ρo) :
    let allocated := H.alloc .rc {ctor, fields}
    Own.Plain.evalRhs tables ρo H (.ctor ctor args) = .ok allocated ∧
    Own.Proof.Den allocated.2 allocated.1 (.ctor ctor logical) ∧
    Balance allocated.2 (holdRoots external held) [allocated.1] ∧
    (∀ v w, Own.Proof.Den H v w → Own.Proof.Den allocated.2 v w) ∧
    ((∃ address next finalMem finalSlots finalLists,
      Gen.AllocatorReady maxClass allocated.2 (placeFresh addresses H.size address) finalMem
        (holdRoots external (allocated.1 :: held))
        context base next limit finalSlots finalLists ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
        {mem := finalMem, ctx := context,
          stack := {caller with env := caller.env.insert x address, dsts := []} :: callers} ∧
      FusedWords (placeFresh addresses H.size address) D bound
        (ρo.insert x allocated.1) (caller.env.insert x address)) ∨
    Sem.Reaches (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
      1 (.resource .heap)) := by
  dsimp only
  obtain ⟨effect, counts, result, preserve⟩ :=
    Own.Plain.evalRhs_alloc_owned (T := tables) arguments arity positive balance den
  refine ⟨effect, result, counts, preserve, ?_⟩
  have input : holdRoots external (fields ++ held) =
      (fun location => holdRoots external held location + refsIn location fields) := by
    funext location
    simp only [holdRoots, refsIn_append]
    omega
  rw [input] at ready
  have output : (fun location => holdRoots external held location +
      refsIn location [(H.alloc .rc {ctor, fields}).1]) =
      holdRoots external ((H.alloc .rc {ctor, fields}).1 :: held) := by
    funext location
    rw [show (H.alloc .rc {ctor, fields}).1 :: held = [(H.alloc .rc {ctor, fields}).1] ++ held from rfl]
    simp only [holdRoots, refsIn_append]
    omega
  rcases allocation_outcome (body := {ctor, fields}) ready (by simpa [arity] using positive)
      (by simpa [arity] using small) tagBound (by simpa [arity] using nobj) nscalar
      (by simpa [arity] using shared) words (by simpa [arity] using wrapperLookup)
      (by simpa [arity] using procedureLookup) registers values caller callers dest with success | failure
  · obtain ⟨address, next, finalMem, finalSlots, finalLists, restored, trace⟩ := success
    rw [output] at restored
    exact .inl ⟨address, next, finalMem, finalSlots, finalLists, restored, trace,
      related.publish real bounded address⟩
  · exact .inr failure

/-- `fused_allocation_instruction` with the fields' tokens given directly. -/
theorem fused_allocation_instruction_of
    {H : Heap} {external : Nat → Nat} {fields held : List RVal} {ρo : Own.Env}
    {logical : List Fir.Val}
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    (arguments : Own.evalArgs ρo args = some fields)
    (den : Sem.Forall2 (Own.Proof.Den H) fields logical)
    (balance : Balance H (holdRoots external held) fields)
    (arity : fields.length = ctor.arity)
    (positive : 0 < ctor.arity) (small : ctor.arity ≤ maxFields)
    (tagBound : ctor.tag ≤ maxTag) (nobj : ctor.nobj = ctor.arity)
    (nscalar : ctor.nscalar = 0) (shared : ctor.fieldKinds = List.replicate ctor.arity .shared)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (holdRoots external (fields ++ held)) context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure bound : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure ctor.arity))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields ctor.arity ctor.tag)))
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
    let allocated := H.alloc .rc {ctor, fields}
    Own.Plain.evalRhs tables ρo H (.ctor ctor args) = .ok allocated ∧
    Own.Proof.Den allocated.2 allocated.1 (.ctor ctor logical) ∧
    Balance allocated.2 (holdRoots external held) [allocated.1] ∧
    (∀ v w, Own.Proof.Den H v w → Own.Proof.Den allocated.2 v w) ∧
    ((∃ address next finalMem finalSlots finalLists,
      Gen.AllocatorReady maxClass allocated.2 (placeFresh addresses H.size address) finalMem
        (holdRoots external (allocated.1 :: held))
        context base next limit finalSlots finalLists ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := caller :: callers} 2
        {mem := finalMem, ctx := context,
          stack := {caller with pos := caller.pos+1, env := caller.env.insert x address, dsts := []} :: callers} ∧
      FusedWords (placeFresh addresses H.size address) (Rt.Proof.Fused lowerTables consumedFunction) bound
        (ρo.insert x allocated.1) (caller.env.insert x address)) ∨
    Sem.Reaches (Lir.semStep P)
      {mem, ctx := context, stack := caller :: callers} 2 (.resource .heap)) := by
  dsimp only
  obtain ⟨words, wordArgs, wordValues, _⟩ :=
    fused_call_operands_words related consumedLookup consumedInstruction lowered arguments
  obtain ⟨env, binding, registers, values⟩ := allocation_bind_arguments wordValues
  let entry : Lir.Frame := {fn := wrapper, label := 0, pos := 0, env}
  let suspended : Lir.Frame := {caller with pos := caller.pos+1, dsts := [x]}
  have enter : Lir.enter P wrapper words = some entry := by
    simp [Lir.enter, wrapperLookup, allocationWrapper, ← arity, binding, entry]
  have callStep := Lir.step_call (p := P) (mem := mem) (ctx := context)
    (fr := caller) (rest := callers) functionLookup blockLookup position statement wordArgs enter
  obtain ⟨effect, result, counts, preserve, outcome⟩ :=
    fused_allocation_source_wrapper_of tables ctor args x arguments den balance arity positive small
      tagBound nobj nscalar shared ready (fun i => words[i]?.getD 0)
      wrapperLookup procedureLookup registers values suspended callers rfl related real bounded
  refine ⟨effect, result, counts, preserve, ?_⟩
  rcases outcome with ⟨address, next, finalMem, finalSlots, finalLists, restored, trace, represented⟩ | failure
  · refine .inl ⟨address, next, finalMem, finalSlots, finalLists, restored, ?_, represented⟩
    have joined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans trace
    simpa only [entry, suspended, Bool.toNat_true] using joined
  · have joined := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr callStep)) failure
    exact .inr (by simpa only [entry, suspended, Bool.toNat_true] using joined)

/-- `allocation_step` with the fields' tokens given directly. -/
theorem allocation_step_of
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    {kind : Own.Kind} {tail : List Cfg.Instr}
    (head : source.rest = .bind x (.alloc ctor args kind) :: tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {fields held : List RVal} {ρo : Own.Env}
    {logical : List Fir.Val}
    (arguments : Own.evalArgs ρo args = some fields)
    (den : Sem.Forall2 (Own.Proof.Den H) fields logical)
    (balance : Balance H (holdRoots external held) fields)
    (positive : 0 < ctor.arity)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem (holdRoots external (fields ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (real : x < bound) (bounded : Own.Plain.EnvBounded H.size ρo)
    (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ address next mem' slots' lists',
      let allocated := H.alloc .rc {ctor, fields}
      Own.Plain.evalRhs tables ρo H (.ctor ctor args) = .ok allocated ∧
      Own.Proof.Den allocated.2 allocated.1 (.ctor ctor logical) ∧
      Balance allocated.2 (holdRoots external held) [allocated.1] ∧
      (∀ v w, Own.Proof.Den H v w → Own.Proof.Den allocated.2 v w) ∧
      Gen.AllocatorReady maxClass allocated.2 (placeFresh addresses H.size address) mem'
        (holdRoots external (allocated.1 :: held))
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
    obtain ⟨effect, result, counts, preserve, outcome⟩ :=
      fused_allocation_instruction_of tables ctor args x arguments den balance arity positive
        (by omega) tagBound nobj nscalar shared ready
        (raw_public_runtime wrapperLookup) (raw_public_runtime procedureLookup) target callers
        nativeLookup nativeBlockLookup nativePosition statement lowered' blockLookup member registers
        real bounded
    rcases outcome with ⟨address, next, mem', slots', lists', restored, trace, words⟩ | failed
    · exact .inl ⟨address, next, mem', slots', lists', effect, result, counts, preserve,
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
