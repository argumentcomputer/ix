import Compilatrix.IxIR2.CallResources
import Compilatrix.IxIR2.ReservationSteps

/-!
# Committed slots of the physical evaluator

Fresh allocation appends one slot. Freeing or reserving a node leaves that
slot in the arena; only a reservation can be filled in place. Consequently
committed storage is monotone even when live or occupied storage decreases.
These statements concern actual evaluator steps, including suspended calls.
-/

namespace Compilatrix.IxIR2.Eval

open Compilatrix.Ixon (Owned)
open Compilatrix.IxIR1 (Node NodeBox RVal)

def Store.slots (store : Store) : Nat := store.heap.nodes.size

/-- Growth of the backing array agrees exactly with fresh allocation. -/
def SlotGrowth (before after : Store) : Prop :=
  before.slots ≤ after.slots ∧
    after.slots + before.heap.allocs = before.slots + after.heap.allocs

namespace SlotGrowth

theorem refl (store : Store) : SlotGrowth store store := ⟨Nat.le_refl _, rfl⟩

theorem trans {first second third : Store}
    (left : SlotGrowth first second) (right : SlotGrowth second third) :
    SlotGrowth first third := by
  unfold SlotGrowth at *
  omega

theorem allocNode (store : Store) (world : Owned) (node : Node) :
    SlotGrowth store (store.allocNode world node).1 := by
  simp only [SlotGrowth, Store.slots, Store.allocNode_heap, IxIR1.Store.allocNode, Array.size_push]
  omega

theorem setBox (store : Store) (location : Nat) (box : NodeBox) :
    SlotGrowth store (store.setBox location box) := by
  simp [SlotGrowth, Store.slots, IxIR1.Store.setBox]

theorem kill (store : Store) (location : Nat) :
    SlotGrowth store (store.kill location) := by
  simp [SlotGrowth, Store.slots, IxIR1.Store.kill]

theorem reserve (store : Store) (location : Nat) :
    SlotGrowth store (store.reserve location) := by
  simp [SlotGrowth, Store.slots, Store.reserve]

theorem rcTick (store : Store) : SlotGrowth store store.rcTick := refl _
theorem tickResetAttempt (store : Store) : SlotGrowth store store.tickResetAttempt := refl _
theorem tickHotReset (store : Store) : SlotGrowth store store.tickHotReset := refl _
theorem tickColdReset (store : Store) : SlotGrowth store store.tickColdReset := refl _

end SlotGrowth

theorem Store.releaseReservation_slotGrowth {store output : Store} {location : Nat}
    (run : store.releaseReservation location = .ok output) : SlotGrowth store output := by
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.releaseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.releaseReservation, found] at run
      | none =>
          simp only [Store.releaseReservation, found, Except.ok.injEq] at run
          subst output
          exact .refl _

theorem Store.reuseReservation_slotGrowth {store output : Store}
    {location payloadUnits : Nat} {world : Owned} {node : Node}
    (run : store.reuseReservation location world node payloadUnits = .ok output) :
    SlotGrowth store output := by
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.reuseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.reuseReservation, found] at run
      | none =>
          simp only [Store.reuseReservation, found, Except.ok.injEq] at run
          subst output
          simp [SlotGrowth, Store.slots]

theorem retainShared_slotGrowth {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) : SlotGrowth store output := by
  cases value with
  | lit literal => cases run; exact .refl _
  | erased => cases run; exact .refl _
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp [retainShared, found, shared] at run
            subst output
            exact (SlotGrowth.setBox ..).trans (.rcTick _)
          · simp [retainShared, found, shared] at run

theorem RetainSharedMany.slotGrowth {store output : Store} {values : Array RVal}
    (run : RetainSharedMany store values output) : SlotGrowth store output := by
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  have loop : ∀ (values : List RVal) {store output : Store},
      values.foldlM retainShared store = .ok output → SlotGrowth store output := by
    intro values
    induction values with
    | nil => intro store output run; cases run; exact .refl _
    | cons value rest ih =>
        intro store output run
        rw [List.foldlM_cons] at run
        cases head : retainShared store value with
        | error error => simp [head, bind, Except.bind] at run
        | ok middle =>
            simp only [head, bind, Except.bind] at run
            exact (retainShared_slotGrowth head).trans (ih run)
  exact loop values.toList run

theorem releaseSharedWork_slotGrowth {fuel remaining : Nat} {store output : Store}
    {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    SlotGrowth store output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact .refl _
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact .refl _
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
                          Bool.false_eq_true, ↓reduceIte, unitRC, beq_self_eq_true] at run
                        exact (SlotGrowth.rcTick _).trans ((SlotGrowth.kill ..).trans (ih run))
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        exact (SlotGrowth.rcTick _).trans ((SlotGrowth.setBox ..).trans (ih run))
                  · simp [releaseSharedWork, found, shared] at run

theorem releaseShared_slotGrowth {fuel remaining : Nat} {store output : Store}
    {value : RVal} (run : releaseShared fuel store value = .ok (output, remaining)) :
    SlotGrowth store output := releaseSharedWork_slotGrowth run

theorem dropUniqueWork_slotGrowth {fuel remaining : Nat} {store output : Store}
    {values : List RVal}
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) :
    SlotGrowth store output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact .refl _
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact .refl _
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
                        exact (SlotGrowth.kill ..).trans (ih run)
                  · simp [dropUniqueWork, found, unique] at run

theorem dropUnique_slotGrowth {fuel remaining : Nat} {store output : Store}
    {value : RVal} (run : dropUnique fuel store value = .ok (output, remaining)) :
    SlotGrowth store output := dropUniqueWork_slotGrowth run

theorem ApplyTransferCase.slotGrowth {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) : SlotGrowth store target.store := by
  cases classified with
  | erased released => exact releaseSharedWork_slotGrowth released
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      exact (retained.slotGrowth.trans (releaseSharedWork_slotGrowth released)).trans (.allocNode ..)
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      exact retained.slotGrowth.trans (releaseSharedWork_slotGrowth released)
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      exact retained.slotGrowth.trans (releaseSharedWork_slotGrowth released)

theorem ApplyTransfer.slotGrowth {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) : SlotGrowth store target.store := transferred.classify.slotGrowth

theorem InstructionTransferCase.slotGrowth {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store heapFuel
      frame stack instruction target) : SlotGrowth store target.store := by
  cases classified <;> try first
    | exact .refl _
    | exact .allocNode ..
    | exact (SlotGrowth.reserve ..).trans (.tickHotReset _)
    | exact (SlotGrowth.kill ..).trans (.tickHotReset _)
    | exact .reserve ..
    | exact .kill ..
  case allocWithPhysical reused => exact Store.reuseReservation_slotGrowth reused
  case discardPhysical released => exact Store.releaseReservation_slotGrowth released
  case resetSharedCold retained =>
    exact (SlotGrowth.tickResetAttempt _).trans ((SlotGrowth.setBox ..).trans
      ((SlotGrowth.rcTick _).trans ((SlotGrowth.tickColdReset _).trans retained.slotGrowth)))
  case retainShared retained => exact retainShared_slotGrowth retained
  case releaseShared released => exact releaseShared_slotGrowth released
  case dropUnique dropped => exact dropUnique_slotGrowth dropped
  case apply functionResolved argumentsResolved transferred => exact transferred.slotGrowth

theorem TerminatorTransferCase.slotGrowth {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store heapFuel
      frame stack terminator target) : SlotGrowth store target.store := by
  cases classified <;> try exact .refl _
  case retApplyMore resolved noCredits world transferred => exact transferred.slotGrowth

theorem Step.slotGrowth {context : Context} {interpretation : Interpretation}
    {before after : Machine} (stepped : Step context interpretation before after) :
    SlotGrowth before.store after.store := by
  cases before with
  | mk store heapFuel control =>
      cases control with
      | halted value =>
          simp only [Step, step, pure, Except.pure, Except.ok.injEq] at stepped
          subst after
          exact .refl _
      | running frame stack =>
          cases stepped.classify with
          | instruction found bound atIndex classified => exact classified.slotGrowth
          | terminator found bound atIndex classified => exact classified.slotGrowth

namespace Policy

theorem Step.slotGrowth {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {before after : Machine}
    (stepped : Step policy context interpretation before after) : SlotGrowth before.store after.store := by
  rcases stepped.classify with original | ⟨frame, stack, call, _, running, _, called⟩
  · exact original.slotGrowth
  · rw [(suspendCall_resources running called).1]
    exact .refl _

theorem Steps.slotGrowth {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {count : Nat} {before after : Machine}
    (steps : Steps policy context interpretation count before after) : SlotGrowth before.store after.store := by
  induction steps with
  | refl => exact .refl _
  | cons running head tail ih => exact head.slotGrowth.trans ih

/-- Every prefix fits the terminal committed slot count. Peak live nodes
alone cannot supply this bound for the append-only evaluator. -/
theorem runMachine_prefix_slots {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {fuel prefixCount : Nat}
    {initial middle : Machine} {result : Result}
    (run : runMachine policy context interpretation fuel initial = .ok result)
    (prefixSteps : Steps policy context interpretation prefixCount initial middle) :
    middle.store.slots ≤ result.store.slots := by
  obtain ⟨count, _, execution⟩ := runMachine_steps run
  obtain ⟨suffixCount, _, suffix⟩ := prefixSteps.cancelPrefixToHalted execution rfl
  exact suffix.slotGrowth.1

theorem Steps.slot_partition {policy : CreditPolicy} {context : Context}
    {count : Nat} {definition : Function} {arguments : Array RVal} {heapFuel : Nat}
    {machine : Machine}
    (steps : Steps policy context .physical count
      (initialMachine definition arguments heapFuel) machine) :
    machine.store.slots = machine.store.heap.allocs ∧
      machine.store.slots = machine.store.live + machine.presentCredits + machine.store.heap.frees := by
  have growth := steps.slotGrowth.2
  have balance := steps.allocationAccounting (initialMachine_allocationAccounting ..)
  change machine.store.slots + 0 = 0 + machine.store.heap.allocs at growth
  unfold Machine.AllocationAccounting at balance
  omega

end Policy
end Compilatrix.IxIR2.Eval
