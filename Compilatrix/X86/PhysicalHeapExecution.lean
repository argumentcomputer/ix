import Compilatrix.X86.PhysicalHeapFrames
import Compilatrix.IxIR2.CallResources

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (Store RVal Frame Continuation Result)
abbrev PhysicalMachine := IxIR2.Eval.Machine
abbrev PhysicalContext := IxIR2.Eval.Context

inductive Exit where
  | halt
  | resume (caller : Frame) (stack : List Continuation)

def Exit.stack : Exit → List Continuation
  | .halt => []
  | .resume caller stack => .resume caller :: stack

def Exit.reservations (exit : Exit) : List Nat := suspendedReservations exit.stack

def Exit.machine (exit : Exit) (store : Store) (heapFuel : Nat) (value : RVal) : PhysicalMachine :=
  match exit with
  | .halt => ⟨store, heapFuel, .halted value⟩
  | .resume caller stack => ⟨store, heapFuel, .running { caller with values := caller.values.push value } stack⟩

def terminalMachine (result : Result) : PhysicalMachine := ⟨result.store, result.heapRemaining, .halted result.value⟩

def Successful (context : PhysicalContext) (machine : PhysicalMachine) (result : Result) : Prop :=
  ∃ count, IxIR2.Eval.Policy.Steps .suspendedCallsV1 context .physical count machine (terminalMachine result)

theorem Successful.first {context store heapFuel raw stack result}
    (run : Successful context ⟨store, heapFuel, .running raw stack⟩ result) :
    ∃ next, IxIR2.Eval.Policy.Step .suspendedCallsV1 context .physical ⟨store, heapFuel, .running raw stack⟩ next ∧
      Successful context next result := by
  obtain ⟨count, steps⟩ := run
  cases steps with
  | cons running head tail => exact ⟨_, head, _, tail⟩

theorem Exit.returned {context store heapFuel raw source output} {exit : Exit}
    (returned : IxIR2.Eval.TerminatorTransferCase context .physical store heapFuel raw exit.stack (.ret source) output) :
    ∃ value, IxIR2.Eval.resolveAtom raw.values source = .ok value ∧ IxIR2.Eval.NoLiveCredits raw ∧
      output = exit.machine store heapFuel value := by
  cases exit <;> cases returned
  all_goals exact ⟨_, ‹_›, ‹_›, rfl⟩

theorem PrimitiveCode.noCall {schemas constructors scope instruction operation next}
    (code : PrimitiveCode schemas constructors scope instruction operation next) :
    IxIR2.Eval.Policy.DirectCall.ofInstruction? instruction = none := by cases code <;> rfl

theorem physical_instruction_case {context store heapFuel raw stack output body instruction}
    (blockAt : raw.definition.blocks[raw.block]? = some body)
    (instructionAt : body.instructions[raw.pc]? = some instruction)
    (noCall : IxIR2.Eval.Policy.DirectCall.ofInstruction? instruction = none)
    (stepped : IxIR2.Eval.Policy.Step .suspendedCallsV1 context .physical ⟨store, heapFuel, .running raw stack⟩ output) :
    IxIR2.Eval.InstructionTransferCase context .physical store heapFuel raw stack instruction output := by
  obtain ⟨pc, atInstruction⟩ := Array.getElem?_eq_some_iff.mp instructionAt
  have noCall := (IxIR2.Eval.Policy.directCall?_atInstruction blockAt pc atInstruction).trans noCall
  have original : IxIR2.Eval.Step context .physical ⟨store, heapFuel, .running raw stack⟩ output := by
    simpa only [IxIR2.Eval.Policy.Step, IxIR2.Eval.Policy.step, noCall, IxIR2.Eval.Step] using stepped
  cases original.classify with
  | instruction actualBlock actualPc actualInstruction classified =>
      cases Option.some.inj (actualBlock.symm.trans blockAt)
      cases actualInstruction.symm.trans atInstruction
      exact classified
  | terminator actualBlock terminal =>
      cases Option.some.inj (actualBlock.symm.trans blockAt)
      omega

theorem physical_terminator_case {context store heapFuel raw stack output body terminator}
    (blockAt : raw.definition.blocks[raw.block]? = some body)
    (endAt : raw.pc = body.instructions.size) (term : body.terminator = terminator)
    (stepped : IxIR2.Eval.Policy.Step .suspendedCallsV1 context .physical ⟨store, heapFuel, .running raw stack⟩ output) :
    IxIR2.Eval.TerminatorTransferCase context .physical store heapFuel raw stack terminator output := by
  have noCall := IxIR2.Eval.Policy.directCall?_atTerminator blockAt endAt
  have original : IxIR2.Eval.Step context .physical ⟨store, heapFuel, .running raw stack⟩ output := by
    simpa only [IxIR2.Eval.Policy.Step, IxIR2.Eval.Policy.step, noCall, IxIR2.Eval.Step] using stepped
  cases original.classify with
  | instruction actualBlock pc =>
      cases Option.some.inj (actualBlock.symm.trans blockAt)
      omega
  | terminator actualBlock actualPc actualTerm classified =>
      cases Option.some.inj (actualBlock.symm.trans blockAt)
      cases actualTerm.symm.trans term
      exact classified

theorem physical_call_case {context store heapFuel raw stack output body address arguments definition}
    (blockAt : raw.definition.blocks[raw.block]? = some body)
    (instructionAt : body.instructions[raw.pc]? = some (.call address arguments))
    (declared : context.declarations address = some (.fn definition))
    (stepped : IxIR2.Eval.Policy.Step .suspendedCallsV1 context .physical ⟨store, heapFuel, .running raw stack⟩ output) :
    ∃ values, IxIR2.Eval.resolveAtoms raw.values arguments = .ok values ∧
      output = ⟨store, heapFuel, .running ⟨definition, 0, 0, values, #[]⟩ (.resume { raw with pc := raw.pc + 1 } :: stack)⟩ := by
  obtain ⟨pc, atInstruction⟩ := Array.getElem?_eq_some_iff.mp instructionAt
  have atCall := IxIR2.Eval.Policy.directCall?_atInstruction blockAt pc atInstruction
  have suspended : IxIR2.Eval.Policy.suspendCall context ⟨store, heapFuel, .running raw stack⟩ raw stack
      (.function address arguments) = .ok output := by
    simpa only [IxIR2.Eval.Policy.Step, IxIR2.Eval.Policy.step, atCall, IxIR2.Eval.Policy.DirectCall.ofInstruction?] using stepped
  obtain ⟨values, actual, resolved, definitionAt, arity, nonempty, equal⟩ := IxIR2.Eval.Policy.suspendCall_iff.mp suspended
  have same : actual = definition := by
    simpa only [IxIR2.Eval.Policy.DirectCall.definition, declared, Except.ok.injEq] using definitionAt.symm
  subst actual
  exact ⟨values, resolved, equal⟩

def CounterGrowth (before after : Store) (controls : Nat) : Prop :=
  ∀ field, 2 ≤ field → field ≤ 8 → counters before field ≤ counters after field ∧
    counters after field ≤ counters before field + 2 * controls

theorem CounterGrowth.refl (store : Store) (controls : Nat) : CounterGrowth store store controls := by
  intro field lower upper
  omega

theorem CounterGrowth.trans {before middle after first second}
    (left : CounterGrowth before middle first) (right : CounterGrowth middle after second) :
    CounterGrowth before after (first + second) := by
  intro field lower upper
  have := left field lower upper
  have := right field lower upper
  omega

theorem Statistics.counterGrowth {schemas constructors scope instruction operation next before after}
    (statistics : Statistics before after operation)
    (code : PrimitiveCode schemas constructors scope instruction operation next) : CounterGrowth before after 1 := by
  intro field lower upper
  rw [statistics field lower upper]
  have := code.counterDelta_small field
  omega

theorem Statistics.balance {schemas constructors scope instruction operation next before after outside}
    (statistics : Statistics before after operation)
    (code : PrimitiveCode schemas constructors scope instruction operation next)
    (balanced : Balance before scope.owners outside) : Balance after next.owners outside := by
  have allocations := statistics.allocations
  have frees := statistics.frees
  have owners := code.owners
  unfold Balance at *
  omega

def Tree.copiesValid : Tree → Prop
  | .ret .. | .tailCall .. => True
  | .primitive _ next | .call _ _ _ next => next.copiesValid
  | .jump transfer next => HeapTarget.transferValid transfer = true ∧ next.copiesValid
  | .branch _ zeroTransfer zero succTransfer successor =>
      HeapTarget.transferValid zeroTransfer = true ∧ HeapTarget.transferValid succTransfer = true ∧
        zero.copiesValid ∧ successor.copiesValid

theorem plan_copiesValid {program entries exit plan}
    (matched : HeapTarget.Plan.matches program entries exit plan = true) : plan.tree.copiesValid := by
  induction plan with
  | ret | tailCall => trivial
  | primitive entry operation next ih =>
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      exact ih matched.2
  | jump entry transfer next ih =>
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      exact ⟨matched.1.1, ih matched.2⟩
  | branch entry zeroEdge succEdge value zeroTransfer zero succTransfer successor ihZero ihSucc =>
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      exact ⟨matched.1.1.1.1.1.1.2, matched.1.1.1.1.1.2, ihZero matched.1.2, ihSucc matched.2⟩
  | call entry function arguments destination next ih =>
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      split at matched
      · simp at matched
      · simp only [Bool.and_eq_true] at matched
        exact ih matched.2.2

def Declarations (context : PhysicalContext) (entries : Interfaces) : Prop :=
  ∀ (index : Nat) (interface : Interface), entries[index]? = some interface → context.declarations interface.address = some (.fn interface.definition)

/-- The physical prefix ends at exactly one function return. Its saved
continuation is retained as a successful suffix, so calls can compose without
assuming any native execution or an independent callee evaluation oracle. -/
structure Outcome (context : PhysicalContext) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (plans : Array HeapTarget.FunctionPlan) (parameters : Array Nat)
    (layout : HeapArena.Layout) (offset : Nat) (frame : Scalar.Frame layout.region)
    (inputStore : Store) (inputFuel : Nat) (raw : Frame) (exit : Exit)
    (plan : HeapTarget.Plan) (before : State) (final : Result) (outside : Nat) where
  state : State
  store : Store
  heapFuel : Nat
  value : RVal
  count : Nat
  native : HeapRuns.Run layout plans parameters frame plan before state
  steps : IxIR2.Eval.Policy.Steps .suspendedCallsV1 context .physical count
    ⟨inputStore, inputFuel, .running raw exit.stack⟩ (exit.machine store heapFuel value)
  suffix : Successful context (exit.machine store heapFuel value) final
  controls : count ≤ plan.tree.controls (entries.map (·.controls))
  heap : HeapAt context.schemas constructors offset store exit.reservations state.words
  represented : ValueAt layout offset (store.heap.nodes.size - offset) plan.tree.result value (state.registers .rax)
  growth : inputStore.heap.nodes.size ≤ store.heap.nodes.size ∧
    store.heap.nodes.size ≤ inputStore.heap.nodes.size + plan.tree.allocations (entries.map (·.allocations))
  balanced : Balance store plan.tree.result.owners outside
  counters : CounterGrowth inputStore store count

def Outcome.prepend {context constructors entries plans parameters layout offset frame inputStore inputFuel raw
    middleStore middleFuel middleRaw exit plan nextPlan before middle final outside}
    (tail : Outcome context constructors entries plans parameters layout offset frame middleStore middleFuel middleRaw exit nextPlan middle final outside)
    (leadingCount : Nat)
    (leading : IxIR2.Eval.Policy.Steps .suspendedCallsV1 context .physical leadingCount
      ⟨inputStore, inputFuel, .running raw exit.stack⟩ ⟨middleStore, middleFuel, .running middleRaw exit.stack⟩)
    (native : HeapRuns.Run layout plans parameters frame plan before tail.state)
    (result : plan.tree.result = nextPlan.tree.result)
    (controls : leadingCount + tail.count ≤ plan.tree.controls (entries.map (·.controls)))
    (growth : inputStore.heap.nodes.size ≤ tail.store.heap.nodes.size ∧
      tail.store.heap.nodes.size ≤ inputStore.heap.nodes.size + plan.tree.allocations (entries.map (·.allocations)))
    (counters : CounterGrowth inputStore middleStore leadingCount) :
    Outcome context constructors entries plans parameters layout offset frame inputStore inputFuel raw exit plan before final outside := {
  state := tail.state, store := tail.store, heapFuel := tail.heapFuel, value := tail.value, count := leadingCount + tail.count
  native, steps := leading.trans tail.steps, suffix := tail.suffix, controls, heap := tail.heap
  represented := result ▸ tail.represented, growth, balanced := result ▸ tail.balanced
  counters := counters.trans tail.counters }

def Simulates (context : PhysicalContext) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (plans : Array HeapTarget.FunctionPlan) (parameters : Array Nat) (rank : Nat)
    (definition : IxIR2.Function) (block pc : Nat) (scope : Scope) (tree : Tree) : Prop :=
  ∀ (layout : HeapArena.Layout) (offset : Nat) (frame : Scalar.Frame layout.region)
    (store : Store) (heapFuel : Nat) (values : Array RVal) (credits : Array (Option IxIR2.Eval.Credit))
    (before : State) (exit : Exit) (final : Result) (outside : Nat) (plan : HeapTarget.Plan),
    plan.tree = tree → tree.copiesValid → FrameRoom frame rank →
    HeapAt context.schemas constructors offset store (activeReservations ⟨definition, block, pc, values, credits⟩ exit.stack) before.words →
    ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits before →
    Balance store scope.owners outside →
    store.heap.nodes.size - offset + tree.allocations (entries.map (·.allocations)) ≤ capacity →
    Successful context ⟨store, heapFuel, .running ⟨definition, block, pc, values, credits⟩ exit.stack⟩ final →
    Nonempty (Outcome context constructors entries plans parameters layout offset frame store heapFuel
      ⟨definition, block, pc, values, credits⟩ exit plan before final outside)

theorem Simulates.atFrame {context constructors entries plans parameters rank definition block pc scope tree}
    (simulates : Simulates context constructors entries plans parameters rank definition block pc scope tree)
    {layout offset frame store heapFuel raw before exit final outside plan}
    (shape : plan.tree = tree) (definitionAt : raw.definition = definition) (blockAt : raw.block = block) (pcAt : raw.pc = pc)
    (valid : tree.copiesValid) (frames : FrameRoom frame rank)
    (heap : HeapAt context.schemas constructors offset store (activeReservations raw exit.stack) before.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope raw.values raw.credits before)
    (balanced : Balance store scope.owners outside)
    (budget : store.heap.nodes.size - offset + tree.allocations (entries.map (·.allocations)) ≤ capacity)
    (successful : Successful context ⟨store, heapFuel, .running raw exit.stack⟩ final) :
    Nonempty (Outcome context constructors entries plans parameters layout offset frame store heapFuel raw exit plan before final outside) := by
  cases raw with
  | mk actualDefinition actualBlock actualPc values credits =>
      simp only at definitionAt blockAt pcAt
      subst actualDefinition actualBlock actualPc
      exact simulates layout offset frame store heapFuel values credits before exit final outside plan shape valid frames heap locals balanced budget successful

theorem runningMachine_eq {machine : PhysicalMachine} {raw : Frame} {stack : List Continuation}
    (running : machine.control = .running raw stack) :
    machine = ⟨machine.store, machine.heapFuel, .running raw stack⟩ := by
  cases machine
  cases running
  rfl

def FunctionContract (context : PhysicalContext) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (plans : Array HeapTarget.FunctionPlan) (parameters : Array Nat) (index : Nat)
    (interface : Interface) (plan : HeapTarget.FunctionPlan) : Prop :=
  ∀ (layout : HeapArena.Layout) (offset : Nat) (frame : Scalar.Frame layout.region)
    (store : Store) (heapFuel : Nat) (values : Array RVal) (state : State) (exit : Exit) (final : Result) (outside : Nat),
    FrameRoom frame index →
    HeapAt context.schemas constructors offset store (activeReservations ⟨interface.definition, 0, 0, values, #[]⟩ exit.stack) state.words →
    ScopeAt layout offset (store.heap.nodes.size - offset) frame (Scope.initial interface.parameters) values #[] state →
    Balance store (Scope.initial interface.parameters).owners outside →
    store.heap.nodes.size - offset + interface.allocations ≤ capacity →
    Successful context ⟨store, heapFuel, .running ⟨interface.definition, 0, 0, values, #[]⟩ exit.stack⟩ final →
    Nonempty (Outcome context constructors entries plans parameters layout offset frame store heapFuel
      ⟨interface.definition, 0, 0, values, #[]⟩ exit plan.body state final outside)

structure FunctionSummary (context : PhysicalContext) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (plans : Array HeapTarget.FunctionPlan) (parameters : Array Nat) (index : Nat) (interface : Interface) where
  plan : HeapTarget.FunctionPlan
  found : plans[index]? = some plan
  parameterCount : parameters[index]?.getD 0 = interface.parameters.size
  arity : interface.parameters.size = interface.definition.signature.params.size
  nonempty : interface.definition.blocks.isEmpty = false
  small : interface.parameters.size ≤ 2
  result : plan.body.tree.result = interface.result
  allocations : plan.body.tree.allocations (entries.map (·.allocations)) = interface.allocations
  controls : plan.body.tree.controls (entries.map (·.controls)) = interface.controls
  contract : FunctionContract context constructors entries plans parameters index interface plan

def Callees (context : PhysicalContext) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (plans : Array HeapTarget.FunctionPlan) (parameters : Array Nat) (current : Nat) : Prop :=
  ∀ index interface, entries[index]? = some interface → index < current →
    Nonempty (FunctionSummary context constructors entries plans parameters index interface)

end Compilatrix.X86.PhysicalHeap
