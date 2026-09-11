import Ix.Compiler.UniqueReuse.TargetInput
import Ix.Compiler.UniqueReuse.Reclamation

namespace Ix.Compiler.UniqueReuse.Target

open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval

def context (plan : Plan) (reuse : Bool) : Context :=
  .ofProgram (UniqueLower.program plan reuse) (UniqueLower.schemas plan.schema)

def controlCost (plan : Plan) (reuse : Bool) : Nat :=
  (consControl reuse + 1) * plan.values.length + 7

structure MainResult (plan : Plan) (reuse : Bool) (mode : Interpretation) (store : Store) (value : RVal) : Prop where
  owned : RootOwnership store.heap [⟨.unique, value⟩]
  list : ListAt plan.schema store.heap plan.values.reverse value
  allocs : store.heap.allocs = plan.values.length + 2 + freshPerCons reuse mode * plan.values.length
  frees : store.heap.frees = freshPerCons reuse mode * plan.values.length + 1
  reuses : store.heap.reuses = reusesPerCons reuse mode * plan.values.length
  rcops : store.heap.rcops = 0
  live : store.live = plan.values.length + 1
  peak : store.peakLiveNodes = plan.values.length + 2
  attempts : store.resetAttempts = 0
  hot : store.hotResets = 0
  cold : store.coldResets = 0
  payload : store.reusedPayloadUnits = 2 * reusesPerCons reuse mode * plan.values.length

/-- Actual execution of the emitted SSA program. Both selection branches and
both interpretations derive their heap ownership from the empty entry store.
The main program performs no recursive heap traversal, so its independent
heap budget is arbitrary. -/
theorem mainSteps (plan : Plan) (reuse : Bool) (mode : Interpretation) (heapFuel : Nat) :
    ∃ store value,
      Steps (context plan reuse) mode (controlCost plan reuse)
        (initialMachine (UniqueLower.program plan reuse).main #[] heapFuel)
        { store, heapFuel, control := .halted value } ∧
      MainResult plan reuse mode store value := by
  let definition := UniqueLower.mainFunction plan
  let block := definition.blocks[0]'(by simp [definition, UniqueLower.mainFunction])
  let suffix : Array Instr := #[.alloc .unique (nilId plan.schema) #[]]
  obtain ⟨built, registers, inputValue, inputRun, inputResult⟩ :=
    inputSteps (context plan reuse) mode plan.schema plan.values definition block suffix heapFuel rfl rfl
      (inputInstructions_eq plan)
  let initialized := built.allocNode .unique (.ctorN (nilId plan.schema) #[])
  have instructions : block.instructions = inputPrefix plan.schema plan.values ++ suffix := inputInstructions_eq plan
  have bound : plan.values.length + 1 < block.instructions.size := by
    simp [instructions, suffix]
  have accRun := Step.alloc (context := context plan reuse) (interpretation := mode) (arguments := #[])
    (world := .unique) (cid := nilId plan.schema)
    (machine := inputPoint definition built heapFuel (plan.values.length + 1) registers)
    rfl rfl bound
    (by
      change block.instructions[plan.values.length + 1] = .alloc .unique (nilId plan.schema) #[]
      simp only [instructions]
      rw [Array.getElem_append_right (by simp)]
      simp [suffix])
    (nilSchemaAt plan.schema) rfl (nilFields plan.schema built)
  have initializedLive : initialized.1.live = plan.values.length + 2 := by
    simp [initialized, Store.live_allocNode, inputResult.live, Nat.add_assoc]
  have initializedPeak : initialized.1.peakLiveNodes = plan.values.length + 2 := by
    rw [Store.peakLive_allocNode, initializedLive, inputResult.peak]
    omega
  have initializedOwned : RootOwnership initialized.1.heap
      [⟨.unique, inputValue⟩, ⟨.unique, .loc initialized.2⟩] :=
    (ownedNilAllocation inputResult.owned plan.schema).perm (List.Perm.swap _ _ [])
  have call := Step.tailCallFn (context := context plan reuse) (interpretation := mode)
    (definition := UniqueLower.function plan.schema reuse)
    (machine := inputPoint definition initialized.1 heapFuel (plan.values.length + 2)
      (registers.push (.loc initialized.2)))
    rfl rfl (by simp [definition, UniqueLower.mainFunction, inputInstructions_eq]) rfl rfl
    (values := #[.loc initialized.2, inputValue])
    (by
      have atInput : (registers.push (.loc initialized.2))[plan.values.length]? = some inputValue := by
        rw [Array.getElem?_push_lt (by simp [inputResult.size])]
        exact congrArg some (Array.getElem?_eq_some_iff.mp inputResult.last).2
      have atAcc : (registers.push (.loc initialized.2))[plan.values.length + 1]? = some (.loc initialized.2) := by
        rw [← inputResult.size]; simp
      simp [resolveAtoms, resolveAtom, atInput, atAcc]; rfl)
    (by simp [context, Context.ofProgram, UniqueLower.program]) rfl rfl
  obtain ⟨store, value, loopRun, result⟩ := loopSteps (context plan reuse) mode plan.schema reuse plan.values
    initialized.1 heapFuel inputValue (.loc initialized.2) [] rfl initializedOwned
    (inputResult.list.allocNode .unique _) (nilAllocated built.heap plan.schema)
    (by rw [initializedLive, initializedPeak]; exact Nat.le_refl _)
  have history := ((inputRun.trans (accRun.toSteps rfl)).trans (call.toSteps rfl)).trans loopRun
  refine ⟨store, value, ?_, result.owned, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    result.attempts.trans inputResult.attempts, result.hot.trans inputResult.hot,
    result.cold.trans inputResult.cold, ?_⟩
  · have count : plan.values.length + 1 + 1 + 1 + (consControl reuse * plan.values.length + 4) =
        controlCost plan reuse := by simp [controlCost, Nat.add_mul]; omega
    have initialHeap := initialMachine_store_empty definition #[] heapFuel
    dsimp only [initialMachine] at initialHeap
    simpa only [count, initialMachine, inputPoint, UniqueLower.program, definition, initialHeap] using history
  · simpa using result.list
  · rw [result.allocs]
    simp [initialized, IxIR1.Store.allocNode, inputResult.allocs, Nat.add_assoc]
  · rw [result.frees]
    simp [initialized, IxIR1.Store.allocNode, inputResult.frees]
  · rw [result.reuses]
    simp [initialized, IxIR1.Store.allocNode, inputResult.reuses]
  · exact result.rcops.trans inputResult.rcops
  · have live := result.live
    rw [initializedLive] at live
    omega
  · exact result.peak.trans initializedPeak
  · rw [result.payload]
    change built.reusedPayloadUnits + _ = _
    rw [inputResult.payload, Nat.zero_add]

theorem mainRuns (plan : Plan) (reuse : Bool) (mode : Interpretation) (extraControl heapFuel : Nat) :
    ∃ result,
      runMain (context plan reuse) mode (UniqueLower.program plan reuse)
        (controlCost plan reuse + extraControl) heapFuel = .ok result ∧
      MainResult plan reuse mode result.store result.value ∧
      result.controlRemaining = extraControl ∧ result.heapRemaining = heapFuel := by
  obtain ⟨store, value, steps, result⟩ := mainSteps plan reuse mode heapFuel
  refine ⟨⟨store, value, extraControl, heapFuel⟩, ?_, result, rfl, rfl⟩
  rw [runMain_eq_runMachine rfl rfl, steps.runMachine]
  simp [runMachine]

theorem MainResult.reclaims {plan : Plan} {reuse : Bool} {mode : Interpretation} {store : Store} {value : RVal}
    (result : MainResult plan reuse mode store value) :
    ∃ reclaimed,
      dropUnique (2 * plan.values.length + 1) store value = .ok (reclaimed, 0) ∧
      reclaimed.live = 0 ∧ reclaimed.heap.frees = reclaimed.heap.allocs ∧
      Released2 store reclaimed (plan.values.length + 1) [] := by
  obtain ⟨reclaimed, run, empty, released⟩ := release2_complete result.owned result.list (by simpa using result.live)
  refine ⟨reclaimed, by simpa using run, empty, ?_, by simpa using released⟩
  rw [released.allocs, released.frees, result.allocs, result.frees]
  simp only [List.length_reverse]
  omega

end Ix.Compiler.UniqueReuse.Target
