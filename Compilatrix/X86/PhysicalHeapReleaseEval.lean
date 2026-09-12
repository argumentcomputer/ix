import Compilatrix.X86.PhysicalHeapPrimitiveFree

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (Store RVal)

theorem releaseScalarWork {values : List RVal} {store output : Store} {fuel remaining : Nat}
    (scalars : values.all IxIR2.Eval.RVal.isScalar = true)
    (run : IxIR2.Eval.releaseSharedWork fuel store values = .ok (output, remaining)) : output = store := by
  induction fuel generalizing values with
  | zero => cases values <;> simp_all [IxIR2.Eval.releaseSharedWork]
  | succ fuel ih =>
      cases values with
      | nil => cases run; rfl
      | cons value rest =>
          simp only [List.all_cons, Bool.and_eq_true] at scalars
          cases value with
          | loc location => simp [IxIR2.Eval.RVal.isScalar] at scalars
          | lit literal => exact ih scalars.2 run
          | erased => exact ih scalars.2 run

theorem dropScalarWork {values : List RVal} {store output : Store} {fuel remaining : Nat}
    (scalars : values.all IxIR2.Eval.RVal.isScalar = true)
    (run : IxIR2.Eval.dropUniqueWork fuel store values = .ok (output, remaining)) : output = store := by
  induction fuel generalizing values with
  | zero => cases values <;> simp_all [IxIR2.Eval.dropUniqueWork]
  | succ fuel ih =>
      cases values with
      | nil => cases run; rfl
      | cons value rest =>
          simp only [List.all_cons, Bool.and_eq_true] at scalars
          cases value with
          | loc location => simp [IxIR2.Eval.RVal.isScalar] at scalars
          | lit literal => exact ih scalars.2 run
          | erased => exact ih scalars.2 run

theorem scalar_retain {store output : Store} {value : RVal}
    (scalar : IxIR2.Eval.RVal.isScalar value = true)
    (retained : IxIR2.Eval.retainShared store value = .ok output) : output = store := by
  cases value <;> simp_all [IxIR2.Eval.RVal.isScalar, IxIR2.Eval.retainShared]

theorem scalar_release {store output : Store} {value : RVal} {fuel remaining : Nat}
    (scalar : IxIR2.Eval.RVal.isScalar value = true)
    (released : IxIR2.Eval.releaseShared fuel store value = .ok (output, remaining)) : output = store :=
  releaseScalarWork (by simpa using scalar) released

theorem scalar_drop {store output : Store} {value : RVal} {fuel remaining : Nat}
    (scalar : IxIR2.Eval.RVal.isScalar value = true)
    (dropped : IxIR2.Eval.dropUnique fuel store value = .ok (output, remaining)) : output = store :=
  dropScalarWork (by simpa using scalar) dropped

theorem HeapAt.release_node {schemas constructors offset store reserved words location output fuel remaining}
    (heap : HeapAt schemas constructors offset store reserved words)
    (released : IxIR2.Eval.releaseShared fuel store (.loc location) = .ok (output, remaining)) :
    output = releaseStore .shared (store.kill location) := by
  cases fuel with
  | zero => simp [IxIR2.Eval.releaseShared, IxIR2.Eval.releaseSharedWork] at released
  | succ fuel =>
      cases found : store.get? location with
      | none => simp [IxIR2.Eval.releaseShared, IxIR2.Eval.releaseSharedWork, found] at released
      | some box =>
          rcases (heap.live location box found).2 with ⟨content⟩
          by_cases shared : box.world = .shared
          · simp only [IxIR2.Eval.releaseShared, IxIR2.Eval.releaseSharedWork, found, shared,
              bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, content.unique, beq_self_eq_true,
              content.node] at released
            exact releaseScalarWork (by simp [PhysicalScalar.rval, IxIR2.Eval.RVal.isScalar]) released
          · simp [IxIR2.Eval.releaseShared, IxIR2.Eval.releaseSharedWork, found, shared] at released

theorem HeapAt.drop_node {schemas constructors offset store reserved words location output fuel remaining}
    (heap : HeapAt schemas constructors offset store reserved words)
    (dropped : IxIR2.Eval.dropUnique fuel store (.loc location) = .ok (output, remaining)) :
    output = store.kill location := by
  cases fuel with
  | zero => simp [IxIR2.Eval.dropUnique, IxIR2.Eval.dropUniqueWork] at dropped
  | succ fuel =>
      cases found : store.get? location with
      | none => simp [IxIR2.Eval.dropUnique, IxIR2.Eval.dropUniqueWork, found] at dropped
      | some box =>
          rcases (heap.live location box found).2 with ⟨content⟩
          by_cases unique : box.world = .unique
          · simp only [IxIR2.Eval.dropUnique, IxIR2.Eval.dropUniqueWork, found, unique,
              bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, content.node] at dropped
            exact dropScalarWork (by simp [PhysicalScalar.rval, IxIR2.Eval.RVal.isScalar]) dropped
          · simp [IxIR2.Eval.dropUnique, IxIR2.Eval.dropUniqueWork, found, unique] at dropped

end Compilatrix.X86.PhysicalHeap
