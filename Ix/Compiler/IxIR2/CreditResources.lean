import Ix.Compiler.IxIR2.CreditSteps

/-! Logical allocation accounting and the complete all-prefix counter law. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval

/-- Logical execution balances live nodes and frees, and never performs a
physical reuse. Reset diagnostics do not affect either fact. -/
def LogicalEffect (before after : Store) : Prop :=
  HeapBalance before after ∧ after.heap.reuses = before.heap.reuses

theorem LogicalEffect.refl (store : Store) : LogicalEffect store store := ⟨.refl _, rfl⟩

theorem LogicalEffect.trans {first middle last : Store}
    (one : LogicalEffect first middle) (two : LogicalEffect middle last) :
    LogicalEffect first last := ⟨one.1.trans two.1, two.2.trans one.2⟩

theorem LogicalEffect.alloc (store : Store) (world : Ixon.Owned) (node : Node) :
    LogicalEffect store (store.allocNode world node).1 := ⟨.allocNode .., rfl⟩

theorem LogicalEffect.kill {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) : LogicalEffect store (store.kill location) :=
  ⟨.kill found, rfl⟩

theorem LogicalEffect.retain {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) : LogicalEffect store output :=
  ⟨retainShared_heapBalance run, congrArg Counters.reuses (retain_passive run)⟩

theorem LogicalEffect.retainMany {store output : Store} {values : Array RVal}
    (run : RetainSharedMany store values output) : LogicalEffect store output :=
  ⟨run.heapBalance, congrArg Counters.reuses (retainMany_passive run)⟩

theorem LogicalEffect.releaseWork {store output : Store} {fuel remaining : Nat} {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) : LogicalEffect store output :=
  ⟨releaseSharedWork_heapBalance run, congrArg Counters.reuses (releaseWork_passive run)⟩

theorem LogicalEffect.dropWork {store output : Store} {fuel remaining : Nat} {values : List RVal}
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) : LogicalEffect store output :=
  ⟨dropUniqueWork_heapBalance run, congrArg Counters.reuses (dropWork_passive run)⟩

theorem apply_logicalEffect {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {function : RVal} {arguments : Array RVal}
    {resume : Frame} {stack : List Continuation} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function arguments resume stack target) :
    LogicalEffect store target.store := by
  cases transferred.classify with
  | erased released => exact LogicalEffect.releaseWork released
  | papUnder _ _ _ _ retained released _ =>
      exact ((LogicalEffect.retainMany retained).trans
        (LogicalEffect.releaseWork released)).trans (LogicalEffect.alloc ..)
  | papFn _ _ _ _ retained released _ _ _ _ _ =>
      exact (LogicalEffect.retainMany retained).trans (LogicalEffect.releaseWork released)
  | papExtern _ _ _ _ retained released _ _ _ _ _ =>
      exact (LogicalEffect.retainMany retained).trans (LogicalEffect.releaseWork released)

theorem instruction_logicalEffect {context : Context} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context .logical store heapFuel frame stack instruction target) :
    LogicalEffect store target.store := by
  cases classified <;> try contradiction
  case move => exact LogicalEffect.refl _
  case alloc => exact LogicalEffect.alloc ..
  case allocWithAbsent => exact LogicalEffect.alloc ..
  case allocWithLogical => exact LogicalEffect.alloc ..
  case discardAbsent => exact LogicalEffect.refl _
  case discardLogical => exact LogicalEffect.refl _
  case takeUniqueLogical viewed unitRC => exact LogicalEffect.kill viewed.parts.1
  case resetSharedLogicalHot viewed unitRC => exact LogicalEffect.kill viewed.parts.1
  case resetSharedCold target cid schema location box fields output schemaAt resolved viewed many retained =>
    refine ⟨(HeapBalance.setBox (new := { box with rc := box.rc - 1 }) viewed.parts.1).trans retained.heapBalance, ?_⟩
    exact congrArg Counters.reuses (retainMany_passive retained)
  case retainShared retained => exact LogicalEffect.retain retained
  case releaseShared released => exact LogicalEffect.releaseWork released
  case dropUnique dropped => exact LogicalEffect.dropWork dropped
  case freeUnique viewed scalarFields => exact LogicalEffect.kill viewed.parts.1
  case fetch => exact LogicalEffect.refl _
  case callFn => exact LogicalEffect.refl _
  case callSelf => exact LogicalEffect.refl _
  case pappFn => exact LogicalEffect.alloc ..
  case pappExtern => exact LogicalEffect.alloc ..
  case apply transferred => exact apply_logicalEffect transferred
  case extern => exact LogicalEffect.refl _

theorem terminator_logicalEffect {context : Context} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context .logical store heapFuel frame stack terminator target) :
    LogicalEffect store target.store := by
  cases classified <;> first
    | exact LogicalEffect.refl _
    | (apply apply_logicalEffect; assumption)

theorem step_logicalEffect {policy : CreditPolicy} {context : Context} {before after : Machine}
    (stepped : Policy.Step policy context .logical before after) :
    LogicalEffect before.store after.store := by
  rcases stepped.classify with original | ⟨frame, stack, call, _, running, _, called⟩
  · cases original.classify with
    | halted => exact LogicalEffect.refl _
    | instruction _ _ _ classified => exact instruction_logicalEffect classified
    | terminator _ _ _ classified => exact terminator_logicalEffect classified
  · rw [(Policy.suspendCall_resources running called).1]
    exact LogicalEffect.refl _

theorem steps_logicalEffect {policy : CreditPolicy} {context : Context} {before after : Machine}
    {count : Nat} (steps : Policy.Steps policy context .logical count before after) :
    LogicalEffect before.store after.store := by
  induction steps with
  | refl => exact LogicalEffect.refl _
  | cons running head tail ih => exact (step_logicalEffect head).trans ih

theorem HeapRel.counterLaw {mapping : Array Nat} {left right : Store} {credits : Nat}
    (state : HeapRel mapping left right)
    (balanced : left.live + left.heap.frees = left.heap.allocs)
    (logicalReuses : left.heap.reuses = 0)
    (physical : right.live + right.heap.frees + credits = right.heap.allocs) :
    CounterLaw left.snapshot right.snapshot credits := by
  have events := state.events
  change left.heap.allocs + left.heap.reuses = right.heap.allocs + right.heap.reuses at events
  have live := state.heap.live_eq
  exact ⟨by dsimp [Store.snapshot, Store.counters]; omega,
    by dsimp [Store.snapshot, Store.counters]; omega,
    state.rcops, live, state.attempts, state.hot, state.cold⟩

theorem MachineRel.counterLaw {mapping : Array Nat} {left right : Machine}
    (machines : MachineRel mapping left right)
    (balanced : left.store.live + left.store.heap.frees = left.store.heap.allocs)
    (logicalReuses : left.store.heap.reuses = 0)
    (physical : right.AllocationAccounting) :
    CounterLaw left.store.snapshot right.store.snapshot right.presentCredits :=
  machines.heap.counterLaw balanced logicalReuses physical

/-- The full specification's intermediate counter equations hold for every
logical prefix and its actual physical counterpart. All caller reservations
are included in the outstanding-credit term. -/
theorem prefix_resources {policy : CreditPolicy} {context : Context} {definition : Function}
    {heapFuel count : Nat} {left : Machine}
    (steps : Policy.Steps policy context .logical count (initialMachine definition #[] heapFuel) left) :
    ∃ mapping right, Policy.Steps policy context .physical count
        (initialMachine definition #[] heapFuel) right ∧
      MachineRel mapping left right ∧ right.AllocationAccounting ∧
      CounterLaw left.store.snapshot right.store.snapshot right.presentCredits := by
  obtain ⟨mapping, right, targetSteps, machines, _⟩ := steps_related (initial_related definition heapFuel) steps
  have logical := steps_logicalEffect steps
  have balanced : left.store.live + left.store.heap.frees = left.store.heap.allocs := by
    simpa [HeapBalance, initialMachine, Store.live, IxIR1.Store.live] using logical.1
  have noReuses : left.store.heap.reuses = 0 := logical.2
  have physical := targetSteps.allocationAccounting (initialMachine_allocationAccounting ..)
  exact ⟨mapping, right, targetSteps, machines, physical,
    machines.counterLaw balanced noReuses physical⟩

end Ix.Compiler.IxIR2.CreditRefinement
