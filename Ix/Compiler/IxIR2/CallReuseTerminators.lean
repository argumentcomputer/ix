import Ix.Compiler.IxIR2.CallReuseInstructions

/-! CFG edges, returns, tail calls, and residual application preserve the trace relation. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)

theorem creditTakeMany_empty {frame after : Frame} {ids : Array CreditId} {credits : Array Credit}
    (empty : frame.credits = #[]) (taken : CreditTakeMany frame ids after credits) :
    ids = #[] ∧ after = frame ∧ credits = #[] := by
  have sequence := taken.sequence
  have parts : ∀ {frame after : Frame} {ids : List CreditId} {credits : List Credit},
      CreditTakeSequence frame ids after credits → frame.credits = #[] →
      ids = [] ∧ after = frame ∧ credits = [] := by
    intro frame after ids credits sequence empty
    cases sequence with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons head tail =>
        have found := head.target_eq.2
        simp [empty] at found
  obtain ⟨idsEmpty, rfl, creditsEmpty⟩ := parts sequence empty
  exact ⟨by simpa using congrArg List.toArray idsEmpty, rfl,
    by simpa using congrArg List.toArray creditsEmpty⟩

theorem edge_related {limits : Validate.Limits} {validation : Validate.Context}
    {mapping : Array Nat} {block : Block} {left right leftAfter : Frame}
    {edge : Edge} {leftImplicit rightImplicit : Array RVal}
    (frames : FrameRel limits validation mapping block left right)
    (cleared : NoLiveCredits right)
    (implicitValues : RValsIso (MapRel mapping) leftImplicit.toList rightImplicit.toList)
    (transferred : EdgeTransfer left edge leftImplicit leftAfter) :
    ∃ targetBlock rightAfter, EdgeTransfer right edge rightImplicit rightAfter ∧
      FrameRel limits validation mapping targetBlock leftAfter rightAfter := by
  obtain ⟨values, credits, after, targetBlock, resolved, taken, _, blockAt, arity, _, rfl⟩ := transferred.parts
  obtain ⟨idsEmpty, rfl, rfl⟩ := creditTakeMany_empty frames.leftCredits taken
  obtain ⟨targetValues, targetResolved, valuesRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
  have targetAt : right.definition.blocks[edge.target]? =
      some (rewriteBlock limits validation targetBlock) := by
    rw [frames.definition]
    exact rewriteFunction_block blockAt
  have emptyParams := functionReady_credits frames.ready blockAt
  have targetTake : CreditTakeMany right edge.credits right #[] := by
    rw [idsEmpty]
    exact (CreditTakeSequence.nil right).toMany
  have allValues : RValsIso (MapRel mapping) (leftImplicit ++ values).toList
      (rightImplicit ++ targetValues).toList := by
    simpa only [Array.toList_append] using implicitValues.append valuesRel
  refine ⟨targetBlock, _, EdgeTransfer.of_parts targetResolved targetTake cleared targetAt
    (by rw [rewriteBlock_valueParams, ← values_size allValues]; exact arity)
    (by simp [rewriteBlock_creditParams, emptyParams]), ?_⟩
  have entry := FrameRel.atEntry (limits := limits) (validation := validation)
    frames.ready blockAt allValues arity
  simpa only [Array.map_empty, frames.definition] using entry

theorem terminator_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat}
    {block : Block} {leftFrame rightFrame : Frame} {leftStack rightStack : List Continuation}
    {terminator : Terminator} {leftAfter : Machine}
    (contexts : ContextRel limits validation leftContext rightContext)
    (readyContext : ContextReady leftContext)
    (state : HeapState leftContext mapping leftStore rightStore) (fuel : leftFuel ≤ rightFuel)
    (frames : FrameRel limits validation mapping block leftFrame rightFrame)
    (stack : StackRel limits validation mapping leftStack rightStack)
    (cleared : NoLiveCredits rightFrame)
    (classified : TerminatorTransferCase leftContext .physical leftStore leftFuel leftFrame
      leftStack terminator leftAfter) :
    ∃ after rightAfter,
      TerminatorTransferCase rightContext .physical rightStore rightFuel rightFrame
        rightStack terminator rightAfter ∧
      TransferRel limits validation leftContext mapping after leftStore rightStore leftAfter rightAfter := by
  cases classified with
  | jump transferred =>
      obtain ⟨targetBlock, rightAfter, edge, related⟩ := edge_related frames cleared .nil transferred
      exact ⟨mapping, _, .jump edge, ⟨.refl state, fuel, .running related stack⟩⟩
  | switchCtor resolved boxAt node alternativeAt transferred =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      cases valueRel with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
            state.heap.constructorView mapped (ConstructorView.of_box boxAt rfl node)
          obtain ⟨targetBlock, rightAfter, edge, related⟩ := edge_related frames cleared .nil transferred
          exact ⟨mapping, _, .switchCtor targetResolved targetView.parts.1 targetView.parts.2.2
            alternativeAt edge, ⟨.refl state, fuel, .running related stack⟩⟩
  | switchNatZero resolved transferred =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      cases valueRel
      obtain ⟨targetBlock, rightAfter, edge, related⟩ := edge_related frames cleared .nil transferred
      exact ⟨mapping, _, .switchNatZero targetResolved edge, ⟨.refl state, fuel, .running related stack⟩⟩
  | switchNatSucc resolved transferred =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      cases valueRel
      obtain ⟨targetBlock, rightAfter, edge, related⟩ :=
        edge_related frames cleared (.cons .lit .nil) transferred
      exact ⟨mapping, _, .switchNatSucc targetResolved edge, ⟨.refl state, fuel, .running related stack⟩⟩
  | branchPresent lookedUp present transferred =>
      have found := (CreditTake.of_lookup lookedUp).target_eq.2
      simp [frames.leftCredits] at found
  | branchAbsent lookedUp absent transferred =>
      have found := (CreditTake.of_lookup lookedUp).target_eq.2
      simp [frames.leftCredits] at found
  | retResume resolved noCredits world =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      have targetWorld : RVal.hasWorld rightStore rightFrame.definition.signature.result targetValue = true := by
        rw [frames.definition, rewriteFunction_signature]
        exact state.heap.hasWorld valueRel world
      cases stack with
      | cons head tail =>
          cases head with
          | resume caller positive =>
              exact ⟨mapping, _, .retResume targetResolved cleared targetWorld,
                ⟨.refl state, fuel, .running (caller.pushResult positive valueRel) tail⟩⟩
  | retHalt resolved noCredits world =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      have targetWorld : RVal.hasWorld rightStore rightFrame.definition.signature.result targetValue = true := by
        rw [frames.definition, rewriteFunction_signature]
        exact state.heap.hasWorld valueRel world
      cases stack
      exact ⟨mapping, _, .retHalt targetResolved cleared targetWorld,
        ⟨.refl state, fuel, .halted valueRel⟩⟩
  | retApplyMore resolved noCredits world transferred =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      have targetWorld : RVal.hasWorld rightStore rightFrame.definition.signature.result targetValue = true := by
        rw [frames.definition, rewriteFunction_signature]
        exact state.heap.hasWorld valueRel world
      cases stack with
      | cons head tail =>
          cases head with
          | applyMore caller positive arguments =>
              obtain ⟨after, target, targetApply, related⟩ := apply_related contexts readyContext state fuel
                valueRel arguments caller positive tail transferred
              exact ⟨after, target, .retApplyMore targetResolved cleared targetWorld targetApply, related⟩
  | tailCallFn noCredits resolved declaration arity nonempty =>
      obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
      obtain ⟨entryBlock, entry⟩ := FrameRel.functionEntry (limits := limits)
        (validation := validation) (readyContext declaration) argumentsRel arity
      exact ⟨mapping, _, .tailCallFn cleared targetResolved (contexts.function declaration)
        (by simpa only [rewriteFunction_signature, ← values_size argumentsRel] using arity)
        (rewriteFunction_nonempty nonempty), ⟨.refl state, fuel, .running entry stack⟩⟩
  | tailCallSelf noCredits resolved arity nonempty =>
      obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
      obtain ⟨entryBlock, entry⟩ := FrameRel.functionEntry (limits := limits)
        (validation := validation) frames.ready argumentsRel arity
      have targetArity : targetArguments.size = rightFrame.definition.signature.params.size := by
        simpa only [frames.definition, rewriteFunction_signature, ← values_size argumentsRel] using arity
      have targetNonempty : rightFrame.definition.blocks.isEmpty = false := by
        simpa only [frames.definition] using rewriteFunction_nonempty (limits := limits)
          (context := validation) nonempty
      refine ⟨mapping, _, .tailCallSelf cleared targetResolved targetArity targetNonempty,
        ⟨.refl state, fuel, .running (sourceBlock := entryBlock) ?_ stack⟩⟩
      simpa only [frames.definition] using entry

end Ix.Compiler.IxIR2.CallReuse.Sim
