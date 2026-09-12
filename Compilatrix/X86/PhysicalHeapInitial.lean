import Compilatrix.X86.PhysicalHeapFunctions
import Compilatrix.X86.PhysicalScalarSourceHeap
import Init.Data.List.Nat.Sum

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (Store RVal)

/-- The source export consumes one PAP before entering its body. Its dead
physical slot is excluded from the native leaf arena. -/
def initialStore : Bool → Store
  | false => {}
  | true => { heap := PhysicalScalar.invocationHeap }

def initialOffset (baseline : Bool) : Nat := if baseline then 1 else 0

@[simp] theorem initialStore_size (baseline : Bool) :
    (initialStore baseline).heap.nodes.size = initialOffset baseline := by cases baseline <;> rfl

theorem initialStore_empty (baseline : Bool) (location : Nat) :
    (initialStore baseline).get? location = none := by
  cases baseline
  · simp [initialStore, Store.get?, IxIR1.Store.get?]
  · exact PhysicalScalar.invocationHeap.get? location

theorem initialStore_balanced (baseline : Bool) : Balance (initialStore baseline) 0 0 := by
  cases baseline <;> rfl

theorem initialStore_accounted (baseline : Bool) (definition : IxIR2.Function) (values : Array RVal) (fuel : Nat) :
    (IxIR2.Eval.Machine.mk (initialStore baseline) fuel (.running ⟨definition, 0, 0, values, #[]⟩ [])).AllocationAccounting := by
  cases baseline <;> rfl

theorem initialMachine_eq (baseline : Bool) (definition : IxIR2.Function) (values : Array RVal) (fuel : Nat) :
    IxIR2.Eval.initialMachine definition values fuel (initialStore baseline) =
      ⟨initialStore baseline, fuel, .running ⟨definition, 0, 0, values, #[]⟩ []⟩ := by
  cases baseline <;> rfl

theorem initialStore_counter (baseline : Bool) {field : Nat} (lower : 2 ≤ field) (upper : field ≤ 8) :
    UInt64.ofNat (counters (initialStore baseline) field) = HeapHeader.value baseline field ∧
      counters (initialStore baseline) field ≤ 1 := by
  have cases : field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases baseline <;> decide

theorem initialHeap {schemas constructors} (baseline : Bool) (state : State) :
    HeapAt schemas constructors (initialOffset baseline) (initialStore baseline) []
      (HeapHeader.initialState baseline state).words := by
  refine ⟨by simp, by simp, fun location _ => initialStore_empty baseline location, ?_, ?_, ?_, ?_, ?_⟩
  · rw [HeapHeader.initialize_word _ _ (by decide) (by decide)]
    simp [HeapHeader.value]
  · intro field lower upper
    rw [HeapHeader.initialize_word _ _ (by omega) (by omega)]
    exact (initialStore_counter baseline lower upper).1.symm
  · rw [HeapHeader.initialize_word _ _ (by decide) (by decide)]
    simp [HeapHeader.value]
  · intro location box found
    rw [initialStore_empty] at found
    contradiction
  · intro location above below
    rw [initialStore_size] at below
    omega

theorem initialHeap_called {schemas constructors} (baseline : Bool) (workspace : Workspace)
    (entry : HeapTarget.EntryPlan) (state : State) :
    HeapAt schemas constructors (initialOffset baseline) (initialStore baseline) []
      (HeapEntry.called baseline workspace entry state).words := by
  apply (initialHeap baseline (HeapEntry.installArena workspace (HeapEntry.guarded state))).words
  intro index bound
  have above : heapWords ≤ workspace.frame.top := by
    have := workspace.separate
    simp only [Scalar.Frame.stackIndex] at this
    omega
  simp [HeapEntry.called, HeapEntry.prepared, State.call, show index ≠ workspace.frame.top by omega]

theorem entry_arguments {baseline workspace entry state values}
    (arguments : Scalar.ArgumentsAt values state) :
    Scalar.ArgumentsAt values (HeapEntry.called baseline workspace entry state) := by
  refine ⟨arguments.1, ?_⟩
  intro index bound
  have small : index < 2 := Nat.lt_of_lt_of_le bound arguments.1
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl <;>
    simpa [HeapEntry.called, State.call, HeapEntry.prepared_register] using arguments.2 _ bound

theorem ValueVector.scalars {layout offset used} {kinds : List Kind} {words : List Word}
    (allScalar : ∀ kind ∈ kinds, kind = .scalar) (arity : kinds.length = words.length) :
    ValueVector layout offset used kinds (words.map PhysicalScalar.rval) words := by
  induction kinds generalizing words with
  | nil => cases words <;> simp_all only [List.length_nil, List.length_cons, Nat.succ_ne_zero, Nat.zero_ne_add_one]; exact .nil
  | cons kind rest ih =>
      cases words with
      | nil => simp at arity
      | cons word words =>
          have head := allScalar kind (by simp)
          subst kind
          exact .cons (.scalar word) (ih (fun kind member => allScalar kind (by simp [member])) (by simpa using arity))

theorem scalar_owners {parameters : Array Kind} (allScalar : parameters.all (· == .scalar) = true) :
    (Scope.initial parameters).owners = 0 := by
  rw [Scope.initial_owners]
  have scalarList : parameters.toList.all (fun kind => kind == .scalar) = true := by simpa using allScalar
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro number member
  obtain ⟨kind, present, rfl⟩ := List.mem_map.mp member
  have same : kind = .scalar := beq_iff_eq.mp (List.all_eq_true.mp scalarList kind present)
  rw [same]
  rfl

theorem Successful.halted {context store fuel value final}
    (successful : Successful context ⟨store, fuel, .halted value⟩ final) :
    store = final.store ∧ fuel = final.heapRemaining ∧ value = final.value := by
  obtain ⟨count, steps⟩ := successful
  cases steps with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | cons running => cases running

theorem Store.empty_of_live_zero {store : Store} (empty : store.live = 0) : ∀ location, store.get? location = none := by
  rw [Store.live_eq_countP, Array.countP_eq_zero] at empty
  intro location
  unfold Store.get? IxIR1.Store.get?
  cases found : store.heap.nodes[location]? with
  | none => rfl
  | some box =>
      have member := Array.mem_of_getElem? found
      have dead := empty box member
      cases box <;> simp_all

end Compilatrix.X86.PhysicalHeap
