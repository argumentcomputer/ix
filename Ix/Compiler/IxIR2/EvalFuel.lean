import Ix.Compiler.IxIR2.Eval

/-! Successful executions have budget-independent values and heaps. Extra
heap fuel is carried through each step unchanged, then deterministic finite
execution compares runs with a common initial budget. -/

namespace Ix.Compiler.IxIR2.Eval

theorem releaseSharedWork_addFuel {fuel : Nat} {store output : Store}
    {values : List RVal} {remaining : Nat}
    (run : releaseSharedWork fuel store values = .ok (output, remaining))
    (extra : Nat) :
    releaseSharedWork (fuel + extra) store values = .ok (output, remaining + extra) := by
  induction fuel generalizing store values output remaining with
  | zero =>
      cases values with
      | nil =>
          simp [releaseSharedWork] at run
          obtain ⟨rfl, rfl⟩ := run
          simp [releaseSharedWork]
      | cons => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil =>
          simp [releaseSharedWork] at run
          obtain ⟨rfl, rfl⟩ := run
          simp [releaseSharedWork]
      | cons value values =>
          cases value with
          | lit literal =>
              simpa [releaseSharedWork, Nat.succ_add] using ih run
          | erased =>
              simpa [releaseSharedWork, Nat.succ_add] using ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  cases world : box.world with
                  | unique => simp [releaseSharedWork, found, world] at run
                  | shared =>
                      by_cases zero : box.rc = 0
                      · simp [releaseSharedWork, found, world, zero] at run
                      · by_cases unit : box.rc = 1
                        · cases node : box.node with
                          | ctorN cid fields =>
                              simp [releaseSharedWork, Nat.succ_add, found, world,
                                unit, node] at run ⊢
                              exact ih run
                          | papN address arity arguments =>
                              simp [releaseSharedWork, Nat.succ_add, found, world,
                                unit, node] at run ⊢
                              exact ih run
                        · simp [releaseSharedWork, Nat.succ_add, found, world,
                            zero, unit] at run ⊢
                          exact ih run

theorem dropUniqueWork_addFuel {fuel : Nat} {store output : Store}
    {values : List RVal} {remaining : Nat}
    (run : dropUniqueWork fuel store values = .ok (output, remaining))
    (extra : Nat) :
    dropUniqueWork (fuel + extra) store values = .ok (output, remaining + extra) := by
  induction fuel generalizing store values output remaining with
  | zero =>
      cases values with
      | nil =>
          simp [dropUniqueWork] at run
          obtain ⟨rfl, rfl⟩ := run
          simp [dropUniqueWork]
      | cons => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil =>
          simp [dropUniqueWork] at run
          obtain ⟨rfl, rfl⟩ := run
          simp [dropUniqueWork]
      | cons value values =>
          cases value with
          | lit literal =>
              simpa [dropUniqueWork, Nat.succ_add] using ih run
          | erased =>
              simpa [dropUniqueWork, Nat.succ_add] using ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  cases world : box.world with
                  | shared => simp [dropUniqueWork, found, world] at run
                  | unique =>
                      cases node : box.node with
                      | papN => simp [dropUniqueWork, found, world, node] at run
                      | ctorN cid fields =>
                          simp [dropUniqueWork, Nat.succ_add, found, world, node] at run ⊢
                          exact ih run

def Machine.addHeapFuel (machine : Machine) (extra : Nat) : Machine :=
  { machine with heapFuel := machine.heapFuel + extra }

theorem ApplyTransfer.addHeapFuel {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {function : RVal} {arguments : Array RVal}
    {resume : Frame} {stack : List Continuation} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target) (extra : Nat) :
    ApplyTransfer context interpretation store (heapFuel + extra) function
      arguments resume stack (target.addHeapFuel extra) := by
  cases transferred.classify with
  | erased released =>
      exact (ApplyTransferCase.erased (releaseSharedWork_addFuel released extra)).transfer
  | papUnder a b c d e released g =>
      exact (ApplyTransferCase.papUnder a b c d e
        (releaseSharedWork_addFuel released extra) g).transfer
  | papFn a b c d e released g h i j k =>
      exact (ApplyTransferCase.papFn a b c d e
        (releaseSharedWork_addFuel released extra) g h i j k).transfer
  | papExtern a b c d e released g h i j k =>
      exact (ApplyTransferCase.papExtern a b c d e
        (releaseSharedWork_addFuel released extra) g h i j k).transfer

private theorem instructionAddHeapFuel {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store heapFuel frame
      stack instruction target) (extra : Nat) :
    InstructionTransferCase context interpretation store (heapFuel + extra) frame
      stack instruction (target.addHeapFuel extra) := by
  cases classified <;> try (constructor <;> assumption)
  case allocWithLogical a b c d e f g => exact .allocWithLogical a b c d e f g
  case discardLogical a b c => exact .discardLogical a b c
  case releaseShared resolved released =>
    exact .releaseShared resolved (releaseSharedWork_addFuel released extra)
  case dropUnique resolved dropped =>
    exact .dropUnique resolved (dropUniqueWork_addFuel dropped extra)
  case apply a b c transferred => exact .apply a b c (transferred.addHeapFuel extra)

private theorem terminatorAddHeapFuel {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store heapFuel frame
      stack terminator target) (extra : Nat) :
    TerminatorTransferCase context interpretation store (heapFuel + extra) frame
      stack terminator (target.addHeapFuel extra) := by
  cases classified with
  | jump h => exact .jump h
  | switchCtor a b c d e => exact .switchCtor a b c d e
  | switchNatZero a b => exact .switchNatZero a b
  | switchNatSucc a b => exact .switchNatSucc a b
  | branchPresent a b c => exact .branchPresent a b c
  | branchAbsent a b c => exact .branchAbsent a b c
  | retResume a b c => exact .retResume a b c
  | retHalt a b c => exact .retHalt a b c
  | retApplyMore a b c d => exact .retApplyMore a b c (d.addHeapFuel extra)
  | tailCallFn a b c d e => exact .tailCallFn a b c d e
  | tailCallSelf a b c d => exact .tailCallSelf a b c d

theorem Step.addHeapFuel {context : Context} {interpretation : Interpretation}
    {before after : Machine} (stepped : Step context interpretation before after)
    (extra : Nat) :
    Step context interpretation (before.addHeapFuel extra) (after.addHeapFuel extra) := by
  cases stepped.classify with
  | halted => rfl
  | instruction a b c classified => exact (instructionAddHeapFuel classified extra).step a b c
  | terminator a b c classified => exact (terminatorAddHeapFuel classified extra).step a b c

theorem Steps.addHeapFuel {context : Context} {interpretation : Interpretation}
    {count : Nat} {before after : Machine}
    (steps : Steps context interpretation count before after) (extra : Nat) :
    Steps context interpretation count (before.addHeapFuel extra) (after.addHeapFuel extra) := by
  induction steps with
  | refl => exact .refl _
  | cons running head tail ih => exact .cons running (head.addHeapFuel extra) ih

theorem Steps.halted_unique {context : Context} {interpretation : Interpretation}
    {leftCount rightCount : Nat} {before : Machine}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat} {leftValue rightValue : RVal}
    (left : Steps context interpretation leftCount before
      { store := leftStore, heapFuel := leftFuel, control := .halted leftValue })
    (right : Steps context interpretation rightCount before
      { store := rightStore, heapFuel := rightFuel, control := .halted rightValue }) :
    leftCount = rightCount ∧ leftStore = rightStore ∧ leftFuel = rightFuel ∧ leftValue = rightValue := by
  obtain ⟨count, budget, suffix⟩ := left.cancelPrefixToHalted right rfl
  cases suffix with
  | refl => exact ⟨by omega, rfl, rfl, rfl⟩
  | cons running => contradiction

/-- Any two successful main runs of the same program and interpretation
return the same value and complete store, even with different budgets. -/
theorem runMain_success_unique {source : Program} {context : Context}
    {interpretation : Interpretation} {leftControl rightControl leftHeap rightHeap : Nat}
    {left right : Result} (arity : source.main.signature.params.size = 0)
    (nonempty : source.main.blocks.isEmpty = false)
    (leftRun : runMain context interpretation source leftControl leftHeap = .ok left)
    (rightRun : runMain context interpretation source rightControl rightHeap = .ok right) :
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

end Ix.Compiler.IxIR2.Eval
