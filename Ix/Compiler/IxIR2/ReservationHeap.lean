import Ix.Compiler.IxIR2.HeapAccounting

/-!
# Heap exclusion for reserved slots

Ordinary allocation and destruction preserve every existing empty slot. The
only operation that fills such a slot is `reuseReservation`, at the location
named by its consumed credit. These facts apply throughout a callee, including
recursive destruction and dynamic application.
-/

namespace Ix.Compiler.IxIR2.Eval

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1 (RVal Node NodeBox)

def Store.EmptySlot (store : Store) (location : Nat) : Prop :=
  store.heap.nodes[location]? = some none

def EmptySlotsPreserved (before after : Store) : Prop :=
  ∀ location, before.EmptySlot location → after.EmptySlot location

namespace EmptySlotsPreserved

theorem refl (store : Store) : EmptySlotsPreserved store store := fun _ empty => empty

theorem trans {first second third : Store}
    (left : EmptySlotsPreserved first second) (right : EmptySlotsPreserved second third) :
    EmptySlotsPreserved first third := fun location empty => right location (left location empty)

theorem of_nodes {before after : Store} (same : after.heap.nodes = before.heap.nodes) :
    EmptySlotsPreserved before after := by
  intro location empty
  simpa only [Store.EmptySlot, same] using empty

theorem allocNode (store : Store) (world : Owned) (node : Node) :
    EmptySlotsPreserved store (store.allocNode world node).1 := by
  intro location empty
  have bound := (Array.getElem?_eq_some_iff.mp empty).1
  simpa only [Store.EmptySlot, Store.allocNode_heap, IxIR1.Store.allocNode,
    Array.getElem?_push_lt bound, Array.getElem?_eq_getElem bound] using empty

theorem setBox {store : Store} {location : Nat} {old new : NodeBox}
    (found : store.get? location = some old) :
    EmptySlotsPreserved store (store.setBox location new) := by
  intro reserved empty
  have occupied := IxIR1.Sim.nodes_get?_of_get? found
  have different : location ≠ reserved := by
    intro same
    subst reserved
    rw [empty] at occupied
    cases occupied
  simpa only [Store.EmptySlot, Store.setBox, IxIR1.Store.setBox,
    Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne different] using empty

theorem reserve (store : Store) (location : Nat) :
    EmptySlotsPreserved store (store.reserve location) := by
  intro reserved empty
  by_cases same : location = reserved
  · subst reserved
    exact Array.getElem?_setIfInBounds_self_of_lt
      (Array.getElem?_eq_some_iff.mp empty).1
  · simpa only [Store.EmptySlot, Store.reserve,
      Array.getElem?_setIfInBounds_ne same] using empty

theorem kill (store : Store) (location : Nat) :
    EmptySlotsPreserved store (store.kill location) :=
  reserve store location

theorem rcTick (store : Store) : EmptySlotsPreserved store store.rcTick := refl _

end EmptySlotsPreserved

theorem Store.EmptySlot.not_live {store : Store} {location : Nat}
    (empty : store.EmptySlot location) : store.get? location = none := by
  change IxIR1.Store.get? store.heap location = none
  unfold IxIR1.Store.get?
  rw [empty]
  rfl

theorem Store.reserve_empty {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) : (store.reserve location).EmptySlot location := by
  have occupied := IxIR1.Sim.nodes_get?_of_get? found
  exact Array.getElem?_setIfInBounds_self_of_lt
    (Array.getElem?_eq_some_iff.mp occupied).1

theorem retainShared_preservesEmpty {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) : EmptySlotsPreserved store output := by
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
            exact (EmptySlotsPreserved.setBox found).trans (.rcTick _)
          · simp [retainShared, found, shared] at run

theorem RetainSharedMany.preservesEmpty {store output : Store} {values : Array RVal}
    (run : RetainSharedMany store values output) : EmptySlotsPreserved store output := by
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  have loop : ∀ (values : List RVal) {store output : Store},
      values.foldlM retainShared store = .ok output → EmptySlotsPreserved store output := by
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
            exact (retainShared_preservesEmpty head).trans (ih run)
  exact loop values.toList run

theorem releaseSharedWork_preservesEmpty {fuel remaining : Nat} {store output : Store}
    {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    EmptySlotsPreserved store output := by
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
                        exact (EmptySlotsPreserved.rcTick store).trans
                          ((EmptySlotsPreserved.kill _ location).trans (ih run))
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        have tickAt : store.rcTick.get? location = some box := found
                        exact (EmptySlotsPreserved.rcTick store).trans
                          ((EmptySlotsPreserved.setBox tickAt).trans (ih run))
                  · simp [releaseSharedWork, found, shared] at run

theorem dropUniqueWork_preservesEmpty {fuel remaining : Nat} {store output : Store}
    {values : List RVal}
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) :
    EmptySlotsPreserved store output := by
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
                        exact (EmptySlotsPreserved.kill store location).trans (ih run)
                  · simp [dropUniqueWork, found, unique] at run

theorem Store.releaseReservation_preservesEmpty {store output : Store} {location : Nat}
    (run : store.releaseReservation location = .ok output) : EmptySlotsPreserved store output := by
  unfold Store.releaseReservation at run
  split at run
  · cases run
    exact .refl _
  · cases run

/-- Filling one reservation cannot affect any other reserved slot. The
machine credit invariant supplies the inequality from unique ownership. -/
theorem Store.reuseReservation_preservesOther {store output : Store}
    {location other payload : Nat} {world : Owned} {node : Node}
    (run : store.reuseReservation location world node payload = .ok output)
    (different : location ≠ other) (empty : store.EmptySlot other) :
    output.EmptySlot other := by
  unfold Store.reuseReservation at run
  split at run
  · cases run
    simpa only [Store.EmptySlot, Store.withPeak_heap,
      Array.getElem?_setIfInBounds_ne different] using empty
  · cases run

theorem ApplyTransferCase.preservesEmpty {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {arguments : Array RVal} {resume : Frame} {stack : List Continuation}
    {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) : EmptySlotsPreserved store target.store := by
  cases classified with
  | erased released => exact releaseSharedWork_preservesEmpty released
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      exact (retained.preservesEmpty.trans (releaseSharedWork_preservesEmpty released)).trans
        (EmptySlotsPreserved.allocNode _ _ _)
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      exact retained.preservesEmpty.trans (releaseSharedWork_preservesEmpty released)
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      exact retained.preservesEmpty.trans (releaseSharedWork_preservesEmpty released)

theorem ApplyTransfer.preservesEmpty {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {arguments : Array RVal} {resume : Frame} {stack : List Continuation}
    {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) : EmptySlotsPreserved store target.store :=
  transferred.classify.preservesEmpty

end Ix.Compiler.IxIR2.Eval
