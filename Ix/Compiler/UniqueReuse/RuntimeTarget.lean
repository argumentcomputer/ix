import Ix.Compiler.UniqueReuse.Runtime
import Ix.Compiler.UniqueReuse.TargetMain

/-! The actual exported IxIR₂ function starts from a caller-owned list,
allocates its empty accumulator, and enters the selected reversal worker.
The input observations account for the caller's existing allocation. -/

namespace Ix.Compiler.UniqueReuse.Runtime.Target

open Ix.Compiler.IxIR0.UniqueReverse (Schema)
open Ix.Compiler.IxIR1.Sim (RootOwnership)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval
open Ix.Compiler.UniqueReuse.Target

def context (schema : Schema) (reuse : Bool) : Context :=
  .ofProgram (Runtime.program schema reuse) (UniqueLower.schemas schema)

structure Input (schema : Schema) (values : List Nat) (store : Store) (value : RVal) : Prop where
  owned : RootOwnership store.heap [⟨.unique, value⟩]
  list : ListAt schema store.heap values value
  allocs : store.heap.allocs = values.length + 1
  frees : store.heap.frees = 0
  reuses : store.heap.reuses = 0
  rcops : store.heap.rcops = 0
  live : store.live = values.length + 1
  peak : store.peakLiveNodes = values.length + 1
  attempts : store.resetAttempts = 0
  hot : store.hotResets = 0
  cold : store.coldResets = 0
  payload : store.reusedPayloadUnits = 0

def controlCost (reuse : Bool) (length : Nat) : Nat := consControl reuse * length + 6

/-- Caller-side construction, separate from the compiled function. -/
def makeInput (schema : Schema) : List Nat → Store × RVal
  | [] =>
      let allocated := ({} : Store).allocNode .unique (.ctorN (nilId schema) #[])
      (allocated.1, .loc allocated.2)
  | head :: tail =>
      let input := makeInput schema tail
      let allocated := input.1.allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), input.2])
      (allocated.1, .loc allocated.2)

theorem makeInput_valid (schema : Schema) (values : List Nat) :
    Input schema values (makeInput schema values).1 (makeInput schema values).2 := by
  induction values with
  | nil =>
      refine ⟨ownedNilAllocation RootOwnership.empty schema, nilAllocated {} schema,
        rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
      exact Store.live_allocNode {} .unique _
  | cons head tail ih =>
      let input := makeInput schema tail
      have ready : RootOwnership input.1.heap
          (IxIR1.Sim.rootsFor .unique (IxIR1.Sim.nodeChildren (.ctorN (consId schema) #[.lit (.nat head), input.2])) ++ []) :=
        RootOwnership.addNoLocation (value := .lit (.nat head)) rfl ih.owned
      refine ⟨ready.allocNode trivial, consAllocated ih.list head, ?_, ih.frees, ih.reuses, ih.rcops, ?_, ?_,
        ih.attempts, ih.hot, ih.cold, ih.payload⟩
      · simp [makeInput, IxIR1.Store.allocNode, ih.allocs]
      · simp [makeInput, Store.live_allocNode, ih.live]
      · simp only [makeInput]
        rw [Store.peakLive_allocNode, Store.live_allocNode, ih.peak, ih.live]
        simp [Nat.max_eq_right (show tail.length + 1 ≤ tail.length + 1 + 1 by omega)]

theorem inputSteps (schema : Schema) (reuse : Bool) (mode : Interpretation)
    (values : List Nat) (before : Store) (argument : RVal) (heapFuel : Nat)
    (input : Input schema values before argument)
    (distinct : entryAddress schema ≠ functionAddress schema) :
    ∃ after value,
      Steps (context schema reuse) mode (controlCost reuse values.length)
        (initialMachine (targetEntry schema) #[argument] heapFuel before)
        { store := after, heapFuel, control := .halted value } ∧
      MainResult { schema, values } reuse mode after value := by
  let allocated := before.allocNode .unique (.ctorN (nilId schema) #[])
  let entryPoint := fun store pc registers =>
    inputPoint (targetEntry schema) store heapFuel pc registers
  have nilRun := Step.alloc (context := context schema reuse) (interpretation := mode)
    (arguments := #[]) (world := .unique) (cid := nilId schema)
    (machine := entryPoint before 0 #[argument]) rfl rfl (by change 0 < 1; decide) rfl
    (nilSchemaAt schema) rfl (nilFields schema before)
  have call := Step.tailCallFn (context := context schema reuse) (interpretation := mode)
    (definition := UniqueLower.function schema reuse)
    (machine := entryPoint allocated.1 1 (#[argument].push (.loc allocated.2)))
    rfl rfl rfl rfl rfl (values := #[.loc allocated.2, argument]) rfl
    (by simp [context, Context.ofProgram, Runtime.program, distinct]) rfl rfl
  have allocatedLive : allocated.1.live = values.length + 2 := by
    simp [allocated, Store.live_allocNode, input.live, Nat.add_assoc]
  have allocatedPeak : allocated.1.peakLiveNodes = values.length + 2 := by
    rw [Store.peakLive_allocNode, allocatedLive, input.peak]
    omega
  have owned : RootOwnership allocated.1.heap [⟨.unique, argument⟩, ⟨.unique, .loc allocated.2⟩] :=
    (ownedNilAllocation input.owned schema).perm (List.Perm.swap _ _ [])
  obtain ⟨after, value, loopRun, result⟩ := loopSteps (context schema reuse) mode schema reuse values
    allocated.1 heapFuel argument (.loc allocated.2) [] rfl owned
    (input.list.allocNode .unique _) (nilAllocated before.heap schema)
    (by rw [allocatedLive, allocatedPeak]; exact Nat.le_refl _)
  refine ⟨after, value, ?_, result.owned, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    result.attempts.trans input.attempts, result.hot.trans input.hot,
    result.cold.trans input.cold, ?_⟩
  · have history := ((nilRun.toSteps rfl).trans (call.toSteps rfl)).trans loopRun
    have initial : initialMachine (targetEntry schema) #[argument] heapFuel before =
        entryPoint before 0 #[argument] := by
      have peak : max before.peakLiveNodes before.live = before.peakLiveNodes := by
        rw [input.live, input.peak]; omega
      change ({ store := { before with peakLiveNodes := max before.peakLiveNodes before.live }, heapFuel,
                control := .running { definition := targetEntry schema, values := #[argument] } [] } : Machine) = _
      rw [peak]
      rfl
    rw [initial]
    have cost : 1 + 1 + (consControl reuse * values.length + 4) = controlCost reuse values.length := by
      simp only [controlCost]
      omega
    rw [cost] at history
    exact history
  · simpa using result.list
  · rw [result.allocs]
    simp [allocated, IxIR1.Store.allocNode, input.allocs, Nat.add_assoc]
  · rw [result.frees]
    simp [allocated, IxIR1.Store.allocNode, input.frees]
  · rw [result.reuses]
    simp [allocated, IxIR1.Store.allocNode, input.reuses]
  · exact result.rcops.trans input.rcops
  · have live := result.live
    rw [allocatedLive] at live
    simpa using Nat.add_right_cancel live
  · exact result.peak.trans allocatedPeak
  · rw [result.payload]
    change before.reusedPayloadUnits + _ = _
    rw [input.payload, Nat.zero_add]

theorem inputRuns (schema : Schema) (reuse : Bool) (mode : Interpretation)
    (values : List Nat) (before : Store) (argument : RVal) (heapFuel : Nat)
    (input : Input schema values before argument)
    (distinct : entryAddress schema ≠ functionAddress schema) :
    ∃ result,
      runFunction (context schema reuse) mode (targetEntry schema) #[argument]
        (controlCost reuse values.length) heapFuel before = .ok result ∧
      MainResult { schema, values } reuse mode result.store result.value ∧
      result.controlRemaining = 0 ∧ result.heapRemaining = heapFuel := by
  obtain ⟨after, value, steps, result⟩ := inputSteps schema reuse mode values before argument heapFuel input distinct
  exact ⟨⟨after, value, 0, heapFuel⟩,
    by rw [runFunction_eq_runMachine rfl rfl]; exact steps.runMachine_halted,
    result, rfl, rfl⟩

end Ix.Compiler.UniqueReuse.Runtime.Target

namespace Ix.Compiler.UniqueReuse.Runtime

open Ix.Compiler.Ixon (Address Constant)

theorem Compilation.targetRuns {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
    (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    (values : List Nat) (before : IxIR2.Eval.Store) (argument : IxIR1.RVal) (heapFuel : Nat)
    (input : Target.Input compilation.schema values before argument) (mode : IxIR2.Eval.Interpretation) :
    ∃ result,
      IxIR2.Eval.runFunction (Target.context compilation.schema compilation.selection.reuse) mode
        (targetEntry compilation.schema) #[argument] (Target.controlCost compilation.selection.reuse values.length)
        heapFuel before = .ok result ∧
      UniqueReuse.Target.MainResult { schema := compilation.schema, values } compilation.selection.reuse mode result.store result.value ∧
      result.controlRemaining = 0 ∧ result.heapRemaining = heapFuel :=
  Target.inputRuns compilation.schema compilation.selection.reuse mode values before argument heapFuel input compilation.selection.distinct

end Ix.Compiler.UniqueReuse.Runtime
