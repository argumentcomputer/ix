import Ix.Compiler.IxIR2.CallReuseTransition

/-! Complete partial and residual application under a growing history map. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso NodeBoxIso)

structure TransferRel (limits : Validate.Limits) (validation : Validate.Context)
    (context : Context) (before after : Array Nat) (leftBefore rightBefore : Store)
    (leftAfter rightAfter : Machine) : Prop where
  transition : HeapTransition context before after leftBefore leftAfter.store rightBefore rightAfter.store
  fuel : leftAfter.heapFuel ≤ rightAfter.heapFuel
  control : ControlRel limits validation after leftAfter.control rightAfter.control

theorem HeapMap.papView {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {l r : Nat} {box : NodeBox}
    {address : Ixon.Address} {arity : Nat} {captured : Array RVal}
    (mapped : MapRel mapping l r) (found : left.get? l = some box)
    (node : box.node = .papN address arity captured) :
    ∃ targetBox targetCaptured,
      right.get? r = some targetBox ∧ NodeBoxIso (MapRel mapping) box targetBox ∧
      targetBox.node = .papN address arity targetCaptured ∧
      RValsIso (MapRel mapping) captured.toList targetCaptured.toList := by
  obtain ⟨targetBox, targetAt, boxes⟩ := heap.forward mapped found
  have nodes := boxes.node
  rw [node] at nodes
  cases targetNode : targetBox.node with
  | ctorN cid fields => rw [targetNode] at nodes; cases nodes
  | papN targetAddress targetArity targetCaptured =>
      rw [targetNode] at nodes
      cases nodes with
      | pap captured => exact ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, captured⟩

theorem apply_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat}
    {leftFunction rightFunction : RVal} {leftArguments rightArguments : Array RVal}
    {block : Block} {leftResume rightResume : Frame} {leftStack rightStack : List Continuation}
    {leftAfter : Machine}
    (contexts : ContextRel limits validation leftContext rightContext)
    (readyContext : ContextReady leftContext)
    (state : HeapState leftContext mapping leftStore rightStore) (fuel : leftFuel ≤ rightFuel)
    (function : RValIso (MapRel mapping) leftFunction rightFunction)
    (arguments : RValsIso (MapRel mapping) leftArguments.toList rightArguments.toList)
    (resume : FrameRel limits validation mapping block leftResume rightResume)
    (positive : 0 < leftResume.pc) (stack : StackRel limits validation mapping leftStack rightStack)
    (transferred : ApplyTransfer leftContext .physical leftStore leftFuel leftFunction
      leftArguments leftResume leftStack leftAfter) :
    ∃ after rightAfter,
      ApplyTransfer rightContext .physical rightStore rightFuel rightFunction
        rightArguments rightResume rightStack rightAfter ∧
      TransferRel limits validation leftContext mapping after leftStore rightStore leftAfter rightAfter := by
  cases transferred.classify with
  | erased released =>
      cases function
      obtain ⟨rightOut, rightRemaining, targetRun, remaining, transition⟩ :=
        state.releaseWork fuel arguments released
      exact ⟨mapping, _, ApplyTransfer.erased targetRun,
        ⟨transition, remaining, .running (resume.pushResult positive .erased) stack⟩⟩
  | @papUnder location box address arity captured retainedStore releasedStore outHeapFuel
      found shared node capturedUnder retained released totalUnder =>
      cases function with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, capturedRel⟩ :=
            state.heap.papView mapped found node
          obtain ⟨targetRetained, targetRetain, retaining⟩ := state.retainMany capturedRel retained
          obtain ⟨targetReleased, targetFuel, targetRelease, remaining, releasing⟩ :=
            retaining.state.releaseWork fuel (.cons (.loc mapped) .nil) released
          have total : RValsIso (MapRel mapping) (captured ++ leftArguments).toList
              (targetCaptured ++ rightArguments).toList := by
            simpa only [Array.toList_append] using capturedRel.append arguments
          have allocating := releasing.state.alloc (world := .shared)
            (leftNode := .papN address arity (captured ++ leftArguments)) (.pap total) trivial
          have moved := (retaining.trans releasing).trans allocating
          have newValue : RValIso (MapRel (mapping.push targetReleased.heap.nodes.size))
              (.loc releasedStore.heap.nodes.size) (.loc targetReleased.heap.nodes.size) :=
            .loc (by rw [← releasing.state.heap.size]; exact MapRel.fresh ..)
          refine ⟨_, _, ApplyTransfer.papUnder targetAt (boxes.world.symm.trans shared)
            targetNode (by rw [← values_size capturedRel]; exact capturedUnder)
            targetRetain targetRelease (by rw [← values_size total]; exact totalUnder),
            ⟨moved, remaining, .running (sourceBlock := block) ?_ (stack.mono allocating.extension)⟩⟩
          exact (resume.mono allocating.extension).pushResult positive newValue
  | @papFn location box address arity captured retainedStore releasedStore outHeapFuel definition
      found shared node capturedUnder retained released totalEnough declaration papSafe suppliedArity nonempty =>
      cases function with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, capturedRel⟩ :=
            state.heap.papView mapped found node
          obtain ⟨targetRetained, targetRetain, retaining⟩ := state.retainMany capturedRel retained
          obtain ⟨targetReleased, targetFuel, targetRelease, remainingFuel, releasing⟩ :=
            retaining.state.releaseWork fuel (.cons (.loc mapped) .nil) released
          have total : RValsIso (MapRel mapping) (captured ++ leftArguments).toList
              (targetCaptured ++ rightArguments).toList := by
            simpa only [Array.toList_append] using capturedRel.append arguments
          have supplied := values_extract total 0 arity
          have residual : RValsIso (MapRel mapping)
              ((captured ++ leftArguments).extract arity (captured ++ leftArguments).size).toList
              ((targetCaptured ++ rightArguments).extract arity
                (targetCaptured ++ rightArguments).size).toList := by
            simpa only [values_size total] using values_extract total arity (captured ++ leftArguments).size
          obtain ⟨entryBlock, entry⟩ := FrameRel.functionEntry (limits := limits)
            (validation := validation) (readyContext declaration) supplied suppliedArity
          have empty : ((captured ++ leftArguments).extract arity (captured ++ leftArguments).size).isEmpty =
              ((targetCaptured ++ rightArguments).extract arity
                (targetCaptured ++ rightArguments).size).isEmpty := by
            simp only [Array.isEmpty, values_size residual]
          refine ⟨mapping, _, ApplyTransfer.papFn targetAt (boxes.world.symm.trans shared)
            targetNode (by rw [← values_size capturedRel]; exact capturedUnder)
            targetRetain targetRelease (by rw [← values_size total]; exact totalEnough)
            (contexts.function declaration) papSafe
            (by simpa only [rewriteFunction_signature, ← values_size supplied] using suppliedArity)
            (rewriteFunction_nonempty nonempty),
            ⟨retaining.trans releasing, remainingFuel, .running entry (.cons ?_ stack)⟩⟩
          rw [empty]
          split
          · exact .resume resume positive
          · exact .applyMore resume positive residual
  | @papExtern location box address arity expectedArity captured retainedStore releasedStore outHeapFuel value
      found shared node capturedUnder retained released totalEnough declaration suppliedArity remainingEmpty called =>
      cases function with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, capturedRel⟩ :=
            state.heap.papView mapped found node
          obtain ⟨targetRetained, targetRetain, retaining⟩ := state.retainMany capturedRel retained
          obtain ⟨targetReleased, targetFuel, targetRelease, remainingFuel, releasing⟩ :=
            retaining.state.releaseWork fuel (.cons (.loc mapped) .nil) released
          have total : RValsIso (MapRel mapping) (captured ++ leftArguments).toList
              (targetCaptured ++ rightArguments).toList := by
            simpa only [Array.toList_append] using capturedRel.append arguments
          have supplied := values_extract total 0 arity
          have residual : RValsIso (MapRel mapping)
              ((captured ++ leftArguments).extract arity (captured ++ leftArguments).size).toList
              ((targetCaptured ++ rightArguments).extract arity
                (targetCaptured ++ rightArguments).size).toList := by
            simpa only [values_size total] using values_extract total arity (captured ++ leftArguments).size
          obtain ⟨targetCalled, valueRel⟩ := scalarOracle_related contexts supplied called
          refine ⟨mapping, _, ApplyTransfer.papExtern targetAt (boxes.world.symm.trans shared)
            targetNode (by rw [← values_size capturedRel]; exact capturedUnder)
            targetRetain targetRelease (by rw [← values_size total]; exact totalEnough)
            (contexts.extern declaration) (by rw [← values_size supplied]; exact suppliedArity)
            (by simpa only [Array.isEmpty_iff_size_eq_zero, values_size residual] using remainingEmpty)
            targetCalled,
            ⟨retaining.trans releasing, remainingFuel, .running (resume.pushResult positive valueRel) stack⟩⟩

end Ix.Compiler.IxIR2.CallReuse.Sim
