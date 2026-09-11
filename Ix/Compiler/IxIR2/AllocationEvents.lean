import Ix.Compiler.IxIR2.HeapAccounting
import Ix.Compiler.IxIR1.EvalIso

/-!
# Allocation events, independently of physical storage

An allocation instruction either acquires a fresh slot or fills a reserved
slot. Both count as one event. This auxiliary observation is separate from
the semantic heap and value relations.
-/

namespace Ix.Compiler.IxIR2.Eval

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1 (Node NodeBox RVal)

def Store.allocationEvents (store : Store) : Nat :=
  store.heap.allocs + store.heap.reuses

@[simp] theorem Store.allocationEvents_allocNode (store : Store)
    (world : Owned) (node : Node) :
    (store.allocNode world node).1.allocationEvents = store.allocationEvents + 1 := by
  simp [Store.allocationEvents, IxIR1.Store.allocNode]
  omega

@[simp] theorem Store.allocationEvents_setBox (store : Store)
    (location : Nat) (box : NodeBox) :
    (store.setBox location box).allocationEvents = store.allocationEvents := rfl

@[simp] theorem Store.allocationEvents_kill (store : Store) (location : Nat) :
    (store.kill location).allocationEvents = store.allocationEvents := rfl

@[simp] theorem Store.allocationEvents_reserve (store : Store) (location : Nat) :
    (store.reserve location).allocationEvents = store.allocationEvents := rfl

@[simp] theorem Store.allocationEvents_rcTick (store : Store) :
    store.rcTick.allocationEvents = store.allocationEvents := rfl

@[simp] theorem Store.allocationEvents_tickResetAttempt (store : Store) :
    store.tickResetAttempt.allocationEvents = store.allocationEvents := rfl

@[simp] theorem Store.allocationEvents_tickHotReset (store : Store) :
    store.tickHotReset.allocationEvents = store.allocationEvents := rfl

@[simp] theorem Store.allocationEvents_tickColdReset (store : Store) :
    store.tickColdReset.allocationEvents = store.allocationEvents := rfl

theorem Store.releaseReservation_allocationEvents {store output : Store}
    {location : Nat} (run : store.releaseReservation location = .ok output) :
    output.allocationEvents = store.allocationEvents := by
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.releaseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.releaseReservation, found] at run
      | none =>
          simp only [Store.releaseReservation, found, Except.ok.injEq] at run
          subst output
          rfl

theorem Store.reuseReservation_allocationEvents {store output : Store}
    {location payloadUnits : Nat} {world : Owned} {node : Node}
    (run : store.reuseReservation location world node payloadUnits = .ok output) :
    output.allocationEvents = store.allocationEvents + 1 := by
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.reuseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.reuseReservation, found] at run
      | none =>
          simp only [Store.reuseReservation, found, Except.ok.injEq] at run
          subst output
          change store.heap.allocs + (store.heap.reuses + 1) =
            store.heap.allocs + store.heap.reuses + 1
          omega

theorem retainShared_allocationEvents {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) :
    output.allocationEvents = store.allocationEvents := by
  cases value with
  | lit literal => cases run; rfl
  | erased => cases run; rfl
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp [retainShared, found, shared] at run
            subst output
            rfl
          · simp [retainShared, found, shared] at run

theorem RetainSharedMany.allocationEvents {store output : Store}
    {values : Array RVal} (run : RetainSharedMany store values output) :
    output.allocationEvents = store.allocationEvents := by
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  have loop : ∀ (values : List RVal) {store output : Store},
      values.foldlM retainShared store = .ok output →
        output.allocationEvents = store.allocationEvents := by
    intro values
    induction values with
    | nil => intro store output run; cases run; rfl
    | cons value rest ih =>
        intro store output run
        rw [List.foldlM_cons] at run
        cases head : retainShared store value with
        | error error => simp [head, bind, Except.bind] at run
        | ok middle =>
            simp only [head, bind, Except.bind] at run
            exact (ih run).trans (retainShared_allocationEvents head)
  exact loop values.toList run

theorem releaseSharedWork_allocationCounters {fuel remaining : Nat}
    {store output : Store} {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    output.heap.allocs = store.heap.allocs ∧ output.heap.reuses = store.heap.reuses := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact ⟨rfl, rfl⟩
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact ⟨rfl, rfl⟩
      | cons value rest =>
          cases value with
          | lit literal => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unitRC : box.rc = 1
                      · simp only [releaseSharedWork, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unitRC, beq_self_eq_true,
                          Nat.reduceBEq] at run
                        simpa only [Store.kill_heap, Store.rcTick_heap,
                          IxIR1.Store.kill, IxIR1.Store.rcTick] using ih run
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        simpa only [Store.setBox_heap, Store.rcTick_heap,
                          IxIR1.Store.setBox, IxIR1.Store.rcTick] using ih run
                  · simp [releaseSharedWork, found, shared] at run

theorem releaseSharedWork_allocationEvents {fuel remaining : Nat}
    {store output : Store} {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    output.allocationEvents = store.allocationEvents := by
  obtain ⟨allocs, reuses⟩ := releaseSharedWork_allocationCounters run
  simp only [Store.allocationEvents, allocs, reuses]

theorem releaseShared_allocationCounters {fuel remaining : Nat}
    {store output : Store} {value : RVal}
    (run : releaseShared fuel store value = .ok (output, remaining)) :
    output.heap.allocs = store.heap.allocs ∧ output.heap.reuses = store.heap.reuses :=
  releaseSharedWork_allocationCounters run

theorem releaseShared_allocationEvents {fuel remaining : Nat}
    {store output : Store} {value : RVal}
    (run : releaseShared fuel store value = .ok (output, remaining)) :
    output.allocationEvents = store.allocationEvents :=
  releaseSharedWork_allocationEvents run

theorem dropUniqueWork_allocationEvents {fuel remaining : Nat}
    {store output : Store} {values : List RVal}
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) :
    output.allocationEvents = store.allocationEvents := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; rfl
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; rfl
      | cons value rest =>
          cases value with
          | lit literal => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  by_cases unique : box.world = .unique
                  · cases node : box.node with
                    | papN address arity captured => simp [dropUniqueWork, found, unique, node] at run
                    | ctorN cid fields =>
                        simp only [dropUniqueWork, found, unique, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, node] at run
                        simpa only [Store.allocationEvents_kill] using ih run
                  · simp [dropUniqueWork, found, unique] at run

theorem dropUnique_allocationEvents {fuel remaining : Nat}
    {store output : Store} {value : RVal}
    (run : dropUnique fuel store value = .ok (output, remaining)) :
    output.allocationEvents = store.allocationEvents := dropUniqueWork_allocationEvents run

/-- Equality of event increments, without subtraction or an assumption about
the incoming counters. It composes even when the two heaps have different
allocation and reuse histories. -/
def AllocationDelta (baselineBefore baselineAfter rewrittenBefore rewrittenAfter : Store) : Prop :=
  baselineAfter.allocationEvents + rewrittenBefore.allocationEvents =
    baselineBefore.allocationEvents + rewrittenAfter.allocationEvents

namespace AllocationDelta

theorem of_increments {baselineBefore baselineAfter rewrittenBefore rewrittenAfter : Store}
    {count : Nat}
    (baseline : baselineAfter.allocationEvents = baselineBefore.allocationEvents + count)
    (rewritten : rewrittenAfter.allocationEvents = rewrittenBefore.allocationEvents + count) :
    AllocationDelta baselineBefore baselineAfter rewrittenBefore rewrittenAfter := by
  unfold AllocationDelta
  omega

theorem refl (baseline rewritten : Store) : AllocationDelta baseline baseline rewritten rewritten := by
  unfold AllocationDelta
  omega

theorem trans {b₀ b₁ b₂ r₀ r₁ r₂ : Store}
    (first : AllocationDelta b₀ b₁ r₀ r₁) (second : AllocationDelta b₁ b₂ r₁ r₂) :
    AllocationDelta b₀ b₂ r₀ r₂ := by
  unfold AllocationDelta at *
  omega

theorem preserves {b₀ b₁ r₀ r₁ : Store} (delta : AllocationDelta b₀ b₁ r₀ r₁)
    (initial : b₀.allocationEvents = r₀.allocationEvents) :
    b₁.allocationEvents = r₁.allocationEvents := by
  unfold AllocationDelta at delta
  omega

end AllocationDelta

/-- A partial application allocates precisely when its supplied arguments
remain below the closure's arity. All other successful dispatches allocate
nothing during this transfer. -/
def applyAllocationEvents (store : Store) (function : RVal)
    (arguments : Array RVal) : Nat :=
  match function with
  | .loc location =>
      match store.get? location with
      | some box =>
          match box.node with
          | .papN _ arity captured => if (captured ++ arguments).size < arity then 1 else 0
          | _ => 0
      | none => 0
  | _ => 0

theorem applyAllocationEvents_history {baseline rewritten : Store}
    (heap : IxIR1.Sim.HeapHistoryIso baseline.heap rewritten.heap)
    {baselineFunction rewrittenFunction : RVal}
    {baselineArguments rewrittenArguments : Array RVal}
    (function : IxIR1.Sim.RValIso heap.locRel baselineFunction rewrittenFunction)
    (argumentCount : baselineArguments.size = rewrittenArguments.size) :
    applyAllocationEvents baseline baselineFunction baselineArguments =
      applyAllocationEvents rewritten rewrittenFunction rewrittenArguments := by
  cases function with
  | lit => rfl
  | erased => rfl
  | loc locations =>
      rcases heap.related locations with ⟨leftDead, rightDead⟩ |
        ⟨leftBox, rightBox, leftAt, rightAt, boxes⟩
      · simp [applyAllocationEvents, Store.get?, leftDead, rightDead]
      · simp only [applyAllocationEvents, Store.get?, leftAt, rightAt]
        have nodes := boxes.node
        generalize leftBox.node = leftNode at nodes ⊢
        generalize rightBox.node = rightNode at nodes ⊢
        cases nodes with
        | ctor fields => rfl
        | pap captured =>
            have capturedCount := captured.lengths
            simpa only [Array.length_toList, Array.size_append,
              argumentCount] using congrArg
                (fun size => if size + rewrittenArguments.size < _ then 1 else 0) capturedCount

theorem ApplyTransferCase.allocationEvents {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {arguments : Array RVal} {resume : Frame} {stack : List Continuation}
    {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) :
    target.store.allocationEvents = store.allocationEvents +
      applyAllocationEvents store function arguments := by
  cases classified with
  | erased released =>
      simpa [applyAllocationEvents] using releaseSharedWork_allocationEvents released
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      simp only [applyAllocationEvents, boxAt, node, totalUnder, ↓reduceIte,
        Store.allocationEvents_allocNode]
      rw [releaseSharedWork_allocationEvents released, retained.allocationEvents]
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      simp only [applyAllocationEvents, boxAt, node, Nat.not_lt.mpr totalEnough,
        ↓reduceIte, Nat.add_zero]
      exact (releaseSharedWork_allocationEvents released).trans retained.allocationEvents
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      simp only [applyAllocationEvents, boxAt, node, Nat.not_lt.mpr totalEnough,
        ↓reduceIte, Nat.add_zero]
      exact (releaseSharedWork_allocationEvents released).trans retained.allocationEvents

theorem ApplyTransfer.allocationEvents {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {arguments : Array RVal} {resume : Frame} {stack : List Continuation}
    {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) :
    target.store.allocationEvents = store.allocationEvents +
      applyAllocationEvents store function arguments := transferred.classify.allocationEvents

def instructionAllocationEvents (store : Store) (frame : Frame) : Instr → Nat
  | .alloc .. | .allocWith .. | .papp .. => 1
  | .apply functionAtom argumentAtoms =>
      match resolveAtom frame.values functionAtom, resolveAtoms frame.values argumentAtoms with
      | .ok function, .ok arguments => applyAllocationEvents store function arguments
      | _, _ => 0
  | _ => 0

theorem InstructionTransferCase.allocationEvents {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store heapFuel
      frame stack instruction target) :
    target.store.allocationEvents = store.allocationEvents +
      instructionAllocationEvents store frame instruction := by
  cases classified <;> simp only [instructionAllocationEvents, Nat.add_zero,
    Store.allocationEvents_allocNode, Store.allocationEvents_kill,
    Store.allocationEvents_reserve, Store.allocationEvents_tickHotReset,
    Store.allocationEvents_tickResetAttempt]
  case allocWithPhysical reused => exact Store.reuseReservation_allocationEvents reused
  case discardPhysical released => exact Store.releaseReservation_allocationEvents released
  case resetSharedCold retained => simpa using retained.allocationEvents
  case retainShared retained => exact retainShared_allocationEvents retained
  case releaseShared released => exact releaseShared_allocationEvents released
  case dropUnique dropped => exact dropUnique_allocationEvents dropped
  case apply functionResolved argumentsResolved transferred =>
    simpa only [functionResolved, argumentsResolved] using transferred.allocationEvents

def terminatorAllocationEvents (store : Store) (frame : Frame)
    (stack : List Continuation) : Terminator → Nat
  | .ret atom =>
      match stack, resolveAtom frame.values atom with
      | .applyMore arguments _ :: _, .ok value => applyAllocationEvents store value arguments
      | _, _ => 0
  | _ => 0

theorem TerminatorTransferCase.allocationEvents {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store heapFuel
      frame stack terminator target) :
    target.store.allocationEvents = store.allocationEvents +
      terminatorAllocationEvents store frame stack terminator := by
  cases classified <;> simp only [terminatorAllocationEvents, Nat.add_zero]
  case retApplyMore resolved noCredits world transferred =>
    simpa only [resolved] using transferred.allocationEvents

theorem Step.instructionAllocationEvents {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {target : Machine}
    (step : Step context interpretation ⟨store, heapFuel, .running frame stack⟩ target)
    {block : Block} {instruction : Instr}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instructionAt : block.instructions[frame.pc] = instruction) :
    target.store.allocationEvents = store.allocationEvents +
      instructionAllocationEvents store frame instruction := by
  cases step.classify with
  | instruction found bound atIndex classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      exact classified.allocationEvents
  | terminator found terminal atTerminator classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      omega

theorem Step.terminatorAllocationEvents {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {target : Machine}
    (step : Step context interpretation ⟨store, heapFuel, .running frame stack⟩ target)
    {block : Block} {terminator : Terminator}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminatorAt : block.terminator = terminator) :
    target.store.allocationEvents = store.allocationEvents +
      terminatorAllocationEvents store frame stack terminator := by
  cases step.classify with
  | instruction found bound atIndex classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      omega
  | terminator found terminal atTerminator classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      exact classified.allocationEvents

end Ix.Compiler.IxIR2.Eval
