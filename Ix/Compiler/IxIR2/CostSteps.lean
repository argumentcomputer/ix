import Ix.Compiler.IxIR2.CostObservations

/-!
# RC charges and peak observations of successful machine steps

Every allocation occurs at the end of its heap operation. The exact peak
equation therefore includes all internal heap work, even for dynamic apply.
-/

namespace Ix.Compiler.IxIR2.Eval

open Ix.Compiler.IxIR1.CostTrace

private theorem slotSharedRC (box : NodeBox) :
    slotSharedRcPotential (some box) = if box.world = .shared then box.rc else 0 := by
  rcases box with ⟨world, rc, node⟩
  cases world <;> rfl

def resetRCCharge (store : Store) : RVal → Int
  | .loc location =>
      match store.get? location with
      | some box =>
          if box.rc = 1 then -1
          else match box.node with
            | .ctorN _ fields => 2 * (referenceCountList fields.toList : Int)
            | _ => 0
      | none => 0
  | _ => 0

theorem resetRCCharge_history {baseline rewritten : Store}
    (heap : IxIR1.Sim.HeapHistoryIso baseline.heap rewritten.heap)
    {baselineValue rewrittenValue : RVal}
    (values : IxIR1.Sim.RValIso heap.locRel baselineValue rewrittenValue) :
    resetRCCharge baseline baselineValue = resetRCCharge rewritten rewrittenValue := by
  cases values with
  | lit => rfl
  | erased => rfl
  | loc locations =>
      rcases heap.related locations with ⟨leftDead, rightDead⟩ |
        ⟨leftBox, rightBox, leftAt, rightAt, boxes⟩
      · simp [resetRCCharge, Store.get?, leftDead, rightDead]
      · simp only [resetRCCharge, Store.get?, leftAt, rightAt, boxes.rc]
        have nodes := boxes.node
        generalize leftBox.node = leftNode at nodes ⊢
        generalize rightBox.node = rightNode at nodes ⊢
        cases nodes with
        | ctor fields => simp only [referenceCountList_iso fields]
        | pap captured => rfl

def instructionRCCharge (store : Store) (frame : Frame) : Instr → Int
  | .alloc world .. | .allocWith _ world .. => if world = .shared then 1 else 0
  | .papp .. => 1
  | .retainShared atom =>
      match resolveAtom frame.values atom with
      | .ok value => 2 * (referenceCount value : Int)
      | _ => 0
  | .resetShared atom _ =>
      match resolveAtom frame.values atom with
      | .ok value => resetRCCharge store value
      | _ => 0
  | .apply functionAtom argumentAtoms =>
      match resolveAtom frame.values functionAtom, resolveAtoms frame.values argumentAtoms with
      | .ok function, .ok arguments => applyRCCharge store function arguments
      | _, _ => 0
  | _ => 0

theorem InstructionTransferCase.rcCharge {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store heapFuel
      frame stack instruction target) :
    (target.store.amortizedRC : Int) = store.amortizedRC +
      instructionRCCharge store frame instruction := by
  cases classified <;> simp only [instructionRCCharge, Int.add_zero,
    Store.amortizedRC_allocNode, Int.natCast_add, Store.amortizedRC_tickHotReset,
    ↓reduceIte] <;> try rfl
  case alloc => split <;> simp_all
  case allocWithAbsent => split <;> simp_all
  case allocWithLogical => split <;> simp_all
  case allocWithPhysical reused =>
    have counted := (Store.reuseReservation_observations reused).2.1
    split <;> simp_all
  case discardPhysical released =>
    exact congrArg (fun n : Nat => (n : Int))
      (Store.releaseReservation_observations released).2.1
  case takeUniqueLogical viewed unitRC =>
    have removed := Store.amortizedRC_kill viewed.parts.1
    simpa only [slotSharedRC, viewed.parts.2.1, reduceCtorEq, ↓reduceIte, Nat.add_zero]
      using congrArg (fun n : Nat => (n : Int)) removed
  case takeUniquePhysical viewed unitRC =>
    have removed := Store.amortizedRC_reserve viewed.parts.1
    simpa only [slotSharedRC, viewed.parts.2.1, reduceCtorEq, ↓reduceIte, Nat.add_zero]
      using congrArg (fun n : Nat => (n : Int)) removed
  case resetSharedLogicalHot resolved viewed unitRC =>
    have removed := Store.amortizedRC_kill (store := store.tickResetAttempt) viewed.parts.1
    simp only [slotSharedRC, viewed.parts.2.1, ↓reduceIte, unitRC,
      Store.amortizedRC_tickResetAttempt] at removed
    simp only [resolved, resetRCCharge, viewed.parts.1, unitRC, ↓reduceIte]
    omega
  case resetSharedPhysicalHot resolved viewed unitRC =>
    have removed := Store.amortizedRC_reserve (store := store.tickResetAttempt) viewed.parts.1
    simp only [slotSharedRC, viewed.parts.2.1, ↓reduceIte, unitRC,
      Store.amortizedRC_tickResetAttempt] at removed
    simp only [resolved, resetRCCharge, viewed.parts.1, unitRC, ↓reduceIte]
    omega
  case resetSharedCold resolved viewed many retained =>
    have counted := retained.observations.2.1
    have changed := Store.amortizedRC_decrement (store := store.tickResetAttempt)
      viewed.parts.1 viewed.parts.2.1 many
    rw [Store.amortizedRC_tickColdReset, changed, Store.amortizedRC_tickResetAttempt] at counted
    simp only [resolved, resetRCCharge, viewed.parts.1, viewed.parts.2.2]
    split <;> omega
  case retainShared resolved retained =>
    have counted := (retainShared_observations retained).2.1
    simp only [resolved]
    omega
  case releaseShared released =>
    exact congrArg (fun n : Nat => (n : Int)) (releaseShared_observations released).2.1
  case dropUnique dropped =>
    exact congrArg (fun n : Nat => (n : Int)) (dropUnique_observations dropped).2.1
  case freeUnique viewed scalarFields =>
    have removed := Store.amortizedRC_kill viewed.parts.1
    simpa only [slotSharedRC, viewed.parts.2.1, reduceCtorEq, ↓reduceIte, Nat.add_zero]
      using congrArg (fun n : Nat => (n : Int)) removed
  case apply functionResolved argumentsResolved transferred =>
    simpa only [functionResolved, argumentsResolved] using transferred.rcCharge

theorem InstructionTransferCase.peakLive {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store heapFuel
      frame stack instruction target) :
    target.store.peakLiveNodes =
      if instructionAllocationEvents store frame instruction = 0 then store.peakLiveNodes
      else max store.peakLiveNodes target.store.live := by
  cases classified <;> simp only [instructionAllocationEvents, ↓reduceIte,
    Nat.one_ne_zero, Store.peakLive_allocNode] <;> try rfl
  case allocWithPhysical reused => exact (Store.reuseReservation_observations reused).2.2.1
  case discardPhysical released => exact (Store.releaseReservation_observations released).2.2.1
  case resetSharedCold retained => exact retained.observations.2.2.1
  case retainShared retained => exact (retainShared_observations retained).2.2.1
  case releaseShared released => exact (releaseShared_observations released).2.2.1
  case dropUnique dropped => exact (dropUnique_observations dropped).2.2.1
  case apply functionResolved argumentsResolved transferred =>
    simpa only [functionResolved, argumentsResolved] using transferred.peakLive

theorem InstructionTransferCase.live_le {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store heapFuel
      frame stack instruction target) :
    target.store.live ≤ store.live + instructionAllocationEvents store frame instruction := by
  cases classified <;> simp only [instructionAllocationEvents, Nat.add_zero,
    Store.live_allocNode, Nat.le_refl]
  case allocWithPhysical reused => exact Nat.le_of_eq (Store.reuseReservation_accounting reused).1
  case discardPhysical released => exact Nat.le_of_eq (Store.releaseReservation_accounting released).1
  case takeUniqueLogical viewed unitRC => have removed := Store.live_kill viewed.parts.1; omega
  case takeUniquePhysical viewed unitRC => have removed := Store.live_reserve viewed.parts.1; omega
  case resetSharedLogicalHot viewed unitRC =>
    have removed := Store.live_kill (store := store.tickResetAttempt) viewed.parts.1
    change (store.tickResetAttempt.kill _).live + 1 = store.live at removed
    change (store.tickResetAttempt.kill _).live ≤ store.live
    omega
  case resetSharedPhysicalHot viewed unitRC =>
    have removed := Store.live_reserve (store := store.tickResetAttempt) viewed.parts.1
    change (store.tickResetAttempt.reserve _).live + 1 = store.live at removed
    change (store.tickResetAttempt.reserve _).live ≤ store.live
    omega
  case resetSharedCold viewed many retained =>
    have counted := retained.observations.2.2.2
    exact Nat.le_of_eq (counted.trans (Store.live_setBox viewed.parts.1))
  case retainShared retained => exact Nat.le_of_eq (retainShared_observations retained).2.2.2
  case releaseShared released => exact (releaseShared_observations released).2.2.2
  case dropUnique dropped => exact (dropUnique_observations dropped).2.2.2
  case freeUnique viewed scalarFields => have removed := Store.live_kill viewed.parts.1; omega
  case apply functionResolved argumentsResolved transferred =>
    simpa only [functionResolved, argumentsResolved] using transferred.live_le

def terminatorRCCharge (store : Store) (frame : Frame)
    (stack : List Continuation) : Terminator → Int
  | .ret atom =>
      match stack, resolveAtom frame.values atom with
      | .applyMore arguments _ :: _, .ok value => applyRCCharge store value arguments
      | _, _ => 0
  | _ => 0

theorem TerminatorTransferCase.rcCharge {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store heapFuel
      frame stack terminator target) :
    (target.store.amortizedRC : Int) = store.amortizedRC +
      terminatorRCCharge store frame stack terminator := by
  cases classified <;> simp only [terminatorRCCharge, Int.add_zero]
  case retApplyMore resolved noCredits world transferred =>
    simpa only [resolved] using transferred.rcCharge

theorem TerminatorTransferCase.peakLive {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store heapFuel
      frame stack terminator target) :
    target.store.peakLiveNodes =
      if terminatorAllocationEvents store frame stack terminator = 0 then store.peakLiveNodes
      else max store.peakLiveNodes target.store.live := by
  cases classified <;> simp only [terminatorAllocationEvents, ↓reduceIte]
  case retApplyMore resolved noCredits world transferred =>
    simpa only [resolved] using transferred.peakLive

theorem TerminatorTransferCase.live_le {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store heapFuel
      frame stack terminator target) :
    target.store.live ≤ store.live + terminatorAllocationEvents store frame stack terminator := by
  cases classified <;> simp only [terminatorAllocationEvents, Nat.add_zero, Nat.le_refl]
  case retApplyMore resolved noCredits world transferred =>
    simpa only [resolved] using transferred.live_le

theorem InstructionTransferCase.rcops_mono {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store heapFuel
      frame stack instruction target) : store.heap.rcops ≤ target.store.heap.rcops := by
  cases classified <;> try exact Nat.le_refl _
  case allocWithPhysical reused =>
    exact Nat.le_of_eq (Store.reuseReservation_observations reused).1.symm
  case discardPhysical released =>
    exact Nat.le_of_eq (Store.releaseReservation_observations released).1.symm
  case resetSharedCold retained =>
    have counted := retained.observations.1
    change _ = store.heap.rcops + 1 + _ at counted
    dsimp only
    omega
  case retainShared retained =>
    have counted := (retainShared_observations retained).1
    dsimp only
    omega
  case releaseShared released => exact (releaseShared_observations released).1
  case dropUnique dropped => exact Nat.le_of_eq (dropUnique_observations dropped).1.symm
  case apply transferred => exact transferred.rcops_mono

theorem TerminatorTransferCase.rcops_mono {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store heapFuel
      frame stack terminator target) : store.heap.rcops ≤ target.store.heap.rcops := by
  cases classified <;> try exact Nat.le_refl _
  case retApplyMore transferred => exact transferred.rcops_mono

theorem Step.instructionCosts {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {target : Machine}
    (step : Step context interpretation ⟨store, heapFuel, .running frame stack⟩ target)
    {block : Block} {instruction : Instr}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instructionAt : block.instructions[frame.pc] = instruction) :
    (target.store.amortizedRC : Int) = store.amortizedRC +
      instructionRCCharge store frame instruction ∧
    target.store.peakLiveNodes =
      if Eval.instructionAllocationEvents store frame instruction = 0 then store.peakLiveNodes
      else max store.peakLiveNodes target.store.live := by
  cases step.classify with
  | instruction found bound atIndex classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      exact ⟨classified.rcCharge, classified.peakLive⟩
  | terminator found terminal atTerminator classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      omega

theorem Step.terminatorCosts {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {target : Machine}
    (step : Step context interpretation ⟨store, heapFuel, .running frame stack⟩ target)
    {block : Block} {terminator : Terminator}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminatorAt : block.terminator = terminator) :
    (target.store.amortizedRC : Int) = store.amortizedRC +
      terminatorRCCharge store frame stack terminator ∧
    target.store.peakLiveNodes =
      if Eval.terminatorAllocationEvents store frame stack terminator = 0 then store.peakLiveNodes
      else max store.peakLiveNodes target.store.live := by
  cases step.classify with
  | instruction found bound atIndex classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      omega
  | terminator found terminal atTerminator classified =>
      have same := Option.some.inj (found.symm.trans blockAt)
      subst_vars
      exact ⟨classified.rcCharge, classified.peakLive⟩

/-- The stored peak includes the complete successful heap operation. -/
theorem Step.peakRecords {context : Context} {interpretation : Interpretation}
    {before after : Machine} (step : Step context interpretation before after) :
    ∃ events,
      after.store.peakLiveNodes =
        (if events = 0 then before.store.peakLiveNodes
        else max before.store.peakLiveNodes after.store.live) ∧
      after.store.live ≤ before.store.live + events := by
  cases step.classify with
  | halted => exact ⟨0, rfl, Nat.le_refl _⟩
  | instruction found pc atIndex classified => exact ⟨_, classified.peakLive, classified.live_le⟩
  | terminator found pc atTerminator classified => exact ⟨_, classified.peakLive, classified.live_le⟩

theorem Step.peakLive_mono {context : Context} {interpretation : Interpretation}
    {before after : Machine} (step : Step context interpretation before after) :
    before.store.peakLiveNodes ≤ after.store.peakLiveNodes := by
  obtain ⟨events, recorded, _live⟩ := step.peakRecords
  rw [recorded]
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

theorem Step.preservesPeakBound {context : Context} {interpretation : Interpretation}
    {before after : Machine} (step : Step context interpretation before after)
    (initial : before.store.live ≤ before.store.peakLiveNodes) :
    after.store.live ≤ after.store.peakLiveNodes := by
  obtain ⟨events, recorded, live⟩ := step.peakRecords
  rw [recorded]
  split
  · omega
  · exact Nat.le_max_right _ _

theorem Step.rcops_mono {context : Context} {interpretation : Interpretation}
    {before after : Machine} (step : Step context interpretation before after) :
    before.store.heap.rcops ≤ after.store.heap.rcops := by
  cases step.classify with
  | halted => exact Nat.le_refl _
  | instruction found pc atIndex classified => exact classified.rcops_mono
  | terminator found pc atTerminator classified => exact classified.rcops_mono

theorem Steps.costs_mono {context : Context} {interpretation : Interpretation}
    {count : Nat} {before after : Machine}
    (steps : Steps context interpretation count before after) :
    before.store.heap.rcops ≤ after.store.heap.rcops ∧
    before.store.peakLiveNodes ≤ after.store.peakLiveNodes := by
  induction steps with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons running head tail ih =>
      exact ⟨Nat.le_trans head.rcops_mono ih.1, Nat.le_trans head.peakLive_mono ih.2⟩

theorem Steps.preservesPeakBound {context : Context} {interpretation : Interpretation}
    {count : Nat} {before after : Machine}
    (steps : Steps context interpretation count before after)
    (initial : before.store.live ≤ before.store.peakLiveNodes) :
    after.store.live ≤ after.store.peakLiveNodes := by
  induction steps with
  | refl => exact initial
  | cons running head tail ih => exact ih (head.preservesPeakBound initial)

/-- Every intermediate state of a successful execution is bounded by its
actual final counters. This includes reset, branch, and reuse macro states. -/
theorem runMachine_prefix_costs {context : Context} {interpretation : Interpretation}
    {controlFuel prefixCount : Nat} {initial middle : Machine} {result : Result}
    (run : runMachine context interpretation controlFuel initial = .ok result)
    (prefixSteps : Steps context interpretation prefixCount initial middle)
    (initialPeak : initial.store.live ≤ initial.store.peakLiveNodes) :
    middle.store.heap.rcops ≤ result.store.heap.rcops ∧
    middle.store.peakLiveNodes ≤ result.store.peakLiveNodes ∧
    middle.store.live ≤ result.store.peakLiveNodes := by
  obtain ⟨count, _fuel, execution⟩ := runMachine_steps run
  obtain ⟨suffixCount, _count, suffix⟩ := prefixSteps.cancelPrefixToHalted execution rfl
  have costs := suffix.costs_mono
  exact ⟨costs.1, costs.2, Nat.le_trans (prefixSteps.preservesPeakBound initialPeak) costs.2⟩

end Ix.Compiler.IxIR2.Eval
