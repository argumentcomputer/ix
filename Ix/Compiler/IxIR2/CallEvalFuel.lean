import Ix.Compiler.IxIR2.CallEval
import Ix.Compiler.IxIR2.EvalFuel

/-! Successful policy executions have budget-independent values and stores. -/

namespace Ix.Compiler.IxIR2.Eval.Policy

theorem Step.addHeapFuel {policy : CreditPolicy} {context : Context} {interpretation : Interpretation}
    {before after : Machine} (stepped : Step policy context interpretation before after) (extra : Nat) :
    Step policy context interpretation (before.addHeapFuel extra) (after.addHeapFuel extra) := by
  cases policy with
  | callLocalV0 => exact Eval.Step.addHeapFuel stepped extra
  | suspendedCallsV1 =>
      rcases stepped.classify with original | ⟨frame, stack, call, _, running, atCall, suspended⟩
      · exact of_originalStep (original.addHeapFuel extra)
      · obtain ⟨values, definition, resolved, found, arity, nonempty, rfl⟩ := suspendCall_iff.mp suspended
        simp only [Step, step, Machine.addHeapFuel, running, atCall]
        exact suspendCall_iff.mpr ⟨values, definition, resolved, found, arity, nonempty, rfl⟩

theorem Steps.addHeapFuel {policy : CreditPolicy} {context : Context} {interpretation : Interpretation}
    {count : Nat} {before after : Machine}
    (steps : Steps policy context interpretation count before after) (extra : Nat) :
    Steps policy context interpretation count (before.addHeapFuel extra) (after.addHeapFuel extra) := by
  induction steps with
  | refl => exact .refl _
  | cons running head tail ih => exact .cons running (head.addHeapFuel extra) ih

theorem Steps.halted_unique {policy : CreditPolicy} {context : Context} {interpretation : Interpretation}
    {leftCount rightCount : Nat} {before : Machine}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat} {leftValue rightValue : RVal}
    (left : Steps policy context interpretation leftCount before
      { store := leftStore, heapFuel := leftFuel, control := .halted leftValue })
    (right : Steps policy context interpretation rightCount before
      { store := rightStore, heapFuel := rightFuel, control := .halted rightValue }) :
    leftCount = rightCount ∧ leftStore = rightStore ∧ leftFuel = rightFuel ∧ leftValue = rightValue := by
  obtain ⟨count, budget, suffix⟩ := left.cancelPrefixToHalted right rfl
  cases suffix with
  | refl => exact ⟨by omega, rfl, rfl, rfl⟩
  | cons running => contradiction

theorem runMain_success_unique {policy : CreditPolicy} {source : Program} {context : Context}
    {interpretation : Interpretation} {leftControl rightControl leftHeap rightHeap : Nat}
    {left right : Result} (arity : source.main.signature.params.size = 0)
    (nonempty : source.main.blocks.isEmpty = false)
    (leftRun : runMain policy context interpretation source leftControl leftHeap = .ok left)
    (rightRun : runMain policy context interpretation source rightControl rightHeap = .ok right) :
    left.store = right.store ∧ left.value = right.value := by
  rw [runMain_eq_runMachine arity nonempty] at leftRun rightRun
  obtain ⟨leftCount, _, leftSteps⟩ := runMachine_steps leftRun
  obtain ⟨rightCount, _, rightSteps⟩ := runMachine_steps rightRun
  have leftFunded := leftSteps.addHeapFuel rightHeap
  have rightFunded := rightSteps.addHeapFuel leftHeap
  have common : (initialMachine source.main #[] rightHeap).addHeapFuel leftHeap =
      (initialMachine source.main #[] leftHeap).addHeapFuel rightHeap := by
    simp [initialMachine, Machine.addHeapFuel, Nat.add_comm]
  rw [common] at rightFunded
  obtain ⟨_, stores, _, values⟩ := leftFunded.halted_unique rightFunded
  exact ⟨stores, values⟩

end Ix.Compiler.IxIR2.Eval.Policy
