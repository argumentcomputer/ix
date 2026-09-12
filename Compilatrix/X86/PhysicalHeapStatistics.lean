import Compilatrix.X86.PhysicalHeapReservations
import Compilatrix.X86.PhysicalHeapPrimitiveAlloc
import Compilatrix.X86.PhysicalHeapOwners

namespace Compilatrix.X86.PhysicalHeap
open IxIR2.Eval (Store)

def Statistics (before after : Store) (operation : Primitive) : Prop :=
  ∀ field, 2 ≤ field → field ≤ 8 → counters after field = counters before field + operation.counterDelta field

theorem Statistics.allocations {before after operation} (same : Statistics before after operation) :
    after.heap.allocs = before.heap.allocs + operation.allocations := by
  simpa only [counters, Primitive.counterDelta_allocations] using same 2 (by decide) (by decide)

theorem Statistics.frees {before after operation} (same : Statistics before after operation) :
    after.heap.frees = before.heap.frees + operation.frees := by
  simpa only [counters, Primitive.counterDelta_frees] using same 3 (by decide) (by decide)

theorem statistics_move (store : Store) (destination : Nat) (operand : Scalar.Atom) :
    Statistics store store (.move destination operand) := fun _ _ _ => rfl

theorem statistics_nop (store : Store) : Statistics store store .nop := fun _ _ _ => rfl

theorem statistics_fetch (store : Store) (operand : Scalar.Atom) (field destination : Nat) :
    Statistics store store (.fetch operand field destination) := fun _ _ _ => rfl

theorem statistics_alloc (store : Store) (world : Ixon.Owned) (ctor : Constructor) (cid : IxIR2.CtorId)
    (fields : Array IxIR2.Eval.RVal) (operands : Array Scalar.Atom) (destination : Nat) :
    Statistics store (store.allocNode world (.ctorN cid fields)).1 (.alloc world ctor operands destination) :=
  alloc_counters store world (.ctorN cid fields)

theorem statistics_release (store : Store) (world : Ixon.Owned) (location : Nat) (operand : Scalar.Atom) :
    Statistics store (releaseStore world (store.kill location)) (.release world operand) := by
  intro field lower upper
  have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases world <;> simp [counters, Primitive.counterDelta, releaseStore, Store.kill, IxIR1.Store.kill,
      Store.rcTick, IxIR1.Store.rcTick]

theorem statistics_discard {store output : Store} {location : Nat} (index : Nat)
    (released : store.releaseReservation location = .ok output) : Statistics store output (.discard index) := by
  rw [releaseReservation_kill released]
  exact kill_counters store location

theorem statistics_reserve (store : Store) (world : Ixon.Owned) (location : Nat) (ctor : Constructor)
    (operand : Scalar.Atom) (destination credit : Nat) :
    Statistics store (resetStore world (store.reserve location)) (.reserve world ctor operand destination credit) := by
  intro field lower upper
  have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases world <;> simp [counters, Primitive.counterDelta, resetStore, Store.reserve, Store.tickResetAttempt, Store.tickHotReset]

theorem statistics_reuse {store output : Store} {location : Nat} {world : Ixon.Owned} {ctor : Constructor} {node : IxIR1.Node}
    (reused : store.reuseReservation location world node ctor.schema.fields.size = .ok output)
    (credit : Nat) (operands : Array Scalar.Atom) (destination : Nat) :
    Statistics store output (.reuse world ctor credit operands destination) := (reuse_parts reused).2.2

theorem PrimitiveCode.counterDelta_small {schemas constructors scope instruction operation next}
    (code : PrimitiveCode schemas constructors scope instruction operation next) (field : Nat) :
    operation.counterDelta field ≤ 2 := by
  cases code with
  | reuse selected =>
      have := (constructor_sound selected).2.small
      simp only [Primitive.counterDelta]
      split <;> (try split) <;> omega
  | release | drop =>
      split <;> simp only [Primitive.counterDelta] <;> (try split) <;> omega
  | _ => simp only [Primitive.counterDelta] <;> (try split) <;> omega

end Compilatrix.X86.PhysicalHeap
