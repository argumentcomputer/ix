import Ix.Compiler.IxIR2.Borrow.OpenShape
import Ix.Compiler.IxIR1.Sim

namespace Ix.Compiler.IxIR2.Borrow.Open

open Eval

/-- Only instrumentation differs after cancelling one retain/release pair. -/
def bump (store : Store) (count : Nat) : Store :=
  { store with heap := { store.heap with rcops := store.heap.rcops + count } }

@[simp] theorem bump_zero (store : Store) : bump store 0 = store := rfl

@[simp] theorem bump_get (store : Store) (count location : Nat) :
    (bump store count).get? location = store.get? location := rfl

@[simp] theorem bump_set (store : Store) (count location : Nat) (box : NodeBox) :
    (bump store count).setBox location box = bump (store.setBox location box) count := rfl

@[simp] theorem bump_kill (store : Store) (count location : Nat) :
    (bump store count).kill location = bump (store.kill location) count := rfl

@[simp] theorem bump_tick (store : Store) (count : Nat) :
    (bump store count).rcTick = bump store.rcTick count := by
  simp [bump, Store.rcTick, IxIR1.Store.rcTick, Nat.add_right_comm]

theorem releaseWork_bump {fuel remaining : Nat} {store output : Store} {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) (count : Nat) :
    releaseSharedWork fuel (bump store count) values = .ok (bump output count, remaining) := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; rfl
      | cons => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; rfl
      | cons value rest =>
          cases value with
          | lit => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unit : box.rc = 1
                      · simp only [releaseSharedWork, bump_get, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unit, beq_self_eq_true,
                          Nat.reduceBEq, bump_tick, bump_kill] at run ⊢
                        exact ih run
                      · simp only [releaseSharedWork, bump_get, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, beq_iff_eq, zero, unit,
                          bump_tick, bump_set] at run ⊢
                        exact ih run
                  · simp [releaseSharedWork, found, shared] at run

theorem release_bump {fuel remaining : Nat} {store output : Store} {value : RVal}
    (run : releaseShared fuel store value = .ok (output, remaining)) (count : Nat) :
    releaseShared fuel (bump store count) value = .ok (bump output count, remaining) :=
  releaseWork_bump run count

def retained (store : Store) (location : Nat) (box : NodeBox) : Store :=
  (store.setBox location { box with rc := box.rc + 1 }).rcTick

theorem retained_at {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) :
    (retained store location box).get? location = some { box with rc := box.rc + 1 } :=
  IxIR1.Sim.get?_setBox_same found

theorem retain_eq {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) (shared : box.world = .shared) :
    retainShared store (.loc location) = .ok (retained store location box) := by
  simp [retainShared, found, shared, retained]

private theorem setBox_restore {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) : store.setBox location box = store := by
  have slot := IxIR1.Sim.nodes_get?_of_get? found
  obtain ⟨bound, valueAt⟩ := Array.getElem?_eq_some_iff.mp slot
  have slots : store.heap.nodes.setIfInBounds location (some box) = store.heap.nodes := by
    rw [Array.setIfInBounds, dif_pos bound, ← valueAt]
    exact Array.set_getElem_self bound
  simp only [Store.setBox, IxIR1.Store.setBox, Array.set!_eq_setIfInBounds, slots]

/-- The temporary owner protects the entire reachable graph. Its first
release cannot recurse or free any node, even if the original owner aliases
other caller roots. It restores every slot and costs exactly two RC ticks. -/
theorem retain_release_cancel {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) (shared : box.world = .shared)
    (positive : 0 < box.rc) (fuel : Nat) :
    releaseShared (fuel + 1) (retained store location box) (.loc location) =
      .ok (bump store 2, fuel) := by
  have retainedAt := retained_at found
  have nonunit : box.rc + 1 ≠ 1 := by omega
  simp only [releaseShared, releaseSharedWork, retainedAt, shared, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, beq_iff_eq,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, nonunit, Nat.add_sub_cancel]
  have restore := setBox_restore found
  have cancelled : ((retained store location box).rcTick).setBox location box = bump store 2 := by
    simp only [retained, Store.rcTick, Store.setBox, IxIR1.Store.rcTick, IxIR1.Store.setBox,
      Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
    have slots := congrArg (fun s : Store => s.heap.nodes) restore
    simp only [Store.setBox, IxIR1.Store.setBox, Array.set!_eq_setIfInBounds] at slots
    simp only [slots, bump, Nat.add_assoc]
  simpa [← shared] using cancelled

inductive Major where
  | zero
  | succ (field : RVal)
  deriving Repr

def Major.cid (schema : Schema) : Major → CtorId
  | .zero => schema.zero
  | .succ _ => schema.succ

def Major.fields : Major → Array RVal
  | .zero => #[]
  | .succ field => #[field]

def Major.result (schema : Schema) : Major → Nat
  | .zero => schema.zeroResult
  | .succ _ => schema.succResult

def Major.fieldCost : Major → Nat
  | .zero => 0
  | .succ _ => 1

def Major.At (schema : Schema) (major : Major) (store : Store) (location rc : Nat) : Prop :=
  store.get? location = some ⟨.shared, rc, .ctorN (major.cid schema) major.fields⟩

theorem Major.At.bump {schema major store location rc}
    (found : Major.At schema major store location rc) (count : Nat) :
    Major.At schema major (bump store count) location rc := found

theorem Major.At.retained {schema major store location rc}
    (found : Major.At schema major store location rc) :
    Major.At schema major (retained store location ⟨.shared, rc, .ctorN (major.cid schema) major.fields⟩)
      location (rc + 1) := retained_at found

end Ix.Compiler.IxIR2.Borrow.Open
