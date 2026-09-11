import Ix.Compiler.IxIR2.CreditControl
import Ix.Compiler.IxIR2.CreditHeap

/-! Partial application and return-time residual application. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso NodeBoxIso)
open CallReuse.Sim (MapRel HeapMap)

structure TransferRel (before after : Array Nat) (left right : Machine) : Prop where
  heap : HeapRel after left.store right.store
  extension : MapExtends before after
  fuel : left.heapFuel = right.heapFuel
  control : ControlRel after left.control right.control

structure MachineRel (mapping : Array Nat) (left right : Machine) : Prop where
  heap : HeapRel mapping left.store right.store
  fuel : left.heapFuel = right.heapFuel
  control : ControlRel mapping left.control right.control
  reservations : right.ReservationOwnership

theorem TransferRel.machine {before after : Array Nat} {left right : Machine}
    (related : TransferRel before after left right) (owned : right.ReservationOwnership) :
    MachineRel after left right := ⟨related.heap, related.fuel, related.control, owned⟩

theorem HeapRel.fieldWorlds {left right : Store} {mapping : Array Nat}
    (state : HeapRel mapping left right) {leftValues rightValues : Array RVal} {schema : CtorSchema}
    (related : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    (checked : FieldWorlds left schema leftValues) : FieldWorlds right schema rightValues := by
  have forward : ∀ {lefts rights : List RVal}, RValsIso (MapRel mapping) lefts rights →
      FieldValuesWorldForward left right lefts rights := by
    intro lefts rights related
    induction related with
    | nil => exact .nil
    | cons head tail ih => exact .cons (fun _ valid => state.heap.hasWorld head valid) ih
  exact checked.forward (forward related)

theorem HeapRel.papView {left right : Store} {mapping : Array Nat}
    (state : HeapRel mapping left right) {l r : Nat} {box : NodeBox}
    {address : Ixon.Address} {arity : Nat} {captured : Array RVal}
    (mapped : MapRel mapping l r) (found : left.get? l = some box)
    (node : box.node = .papN address arity captured) :
    ∃ targetBox targetCaptured,
      right.get? r = some targetBox ∧ NodeBoxIso (MapRel mapping) box targetBox ∧
      targetBox.node = .papN address arity targetCaptured ∧
      RValsIso (MapRel mapping) captured.toList targetCaptured.toList := by
  obtain ⟨targetBox, targetAt, boxes⟩ := state.heap.forward mapped found
  have nodes := boxes.node
  rw [node] at nodes
  cases targetNode : targetBox.node with
  | ctorN cid fields => rw [targetNode] at nodes; cases nodes
  | papN targetAddress targetArity targetCaptured =>
      rw [targetNode] at nodes
      cases nodes with
      | pap captured => exact ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, captured⟩

/-- Dynamic dispatch preserves the actual result and the remaining traversal
budget. The same proof serves ordinary application and every `applyMore`
continuation, while retaining all caller credit files. -/
theorem apply_related {context : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {heapFuel : Nat}
    {leftFunction rightFunction : RVal} {leftArguments rightArguments : Array RVal}
    {leftResume rightResume : Frame} {leftStack rightStack : List Continuation}
    {leftAfter : Machine}
    (state : HeapRel mapping leftStore rightStore)
    (function : RValIso (MapRel mapping) leftFunction rightFunction)
    (arguments : RValsIso (MapRel mapping) leftArguments.toList rightArguments.toList)
    (resume : FrameRel mapping leftResume rightResume)
    (stack : StackRel mapping leftStack rightStack)
    (transferred : ApplyTransfer context .logical leftStore heapFuel leftFunction
      leftArguments leftResume leftStack leftAfter) :
    ∃ after rightAfter,
      ApplyTransfer context .physical rightStore heapFuel rightFunction
        rightArguments rightResume rightStack rightAfter ∧
      TransferRel mapping after leftAfter rightAfter := by
  cases transferred.classify with
  | erased released =>
      cases function
      obtain ⟨rightOut, targetRun, heap⟩ := state.releaseWork arguments released
      exact ⟨mapping, _, .erased targetRun,
        ⟨heap, MapExtends.refl _, rfl, .running (resume.push .erased) stack⟩⟩
  | @papUnder location box address arity captured retainedStore releasedStore remaining
      found shared node capturedUnder retained released totalUnder =>
      cases function with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, capturedRel⟩ :=
            state.papView mapped found node
          obtain ⟨targetRetained, targetRetain, retaining⟩ := state.retainMany capturedRel retained
          obtain ⟨targetReleased, targetRelease, releasing⟩ :=
            retaining.releaseWork (.cons (.loc mapped) .nil) released
          have total : RValsIso (MapRel mapping) (captured ++ leftArguments).toList
              (targetCaptured ++ rightArguments).toList := by
            simpa only [Array.toList_append] using capturedRel.append arguments
          have allocating := releasing.alloc (world := .shared)
            (leftNode := .papN address arity (captured ++ leftArguments)) (.pap total)
          have extension : MapExtends mapping (mapping.push targetReleased.heap.nodes.size) :=
            MapExtends.push mapping targetReleased.heap.nodes.size
          have newValue : RValIso (MapRel (mapping.push targetReleased.heap.nodes.size))
              (.loc releasedStore.heap.nodes.size) (.loc targetReleased.heap.nodes.size) :=
            .loc (by rw [← releasing.heap.size]; exact MapRel.fresh ..)
          exact ⟨_, _, .papUnder targetAt (boxes.world.symm.trans shared)
            targetNode (by rw [← values_size capturedRel]; exact capturedUnder)
            targetRetain targetRelease (by rw [← values_size total]; exact totalUnder),
            ⟨allocating, extension, rfl,
              .running ((resume.mono extension).push newValue) (stack.mono extension)⟩⟩
  | @papFn location box address arity captured retainedStore releasedStore remaining definition
      found shared node capturedUnder retained released totalEnough declaration papSafe suppliedArity nonempty =>
      cases function with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, capturedRel⟩ :=
            state.papView mapped found node
          obtain ⟨targetRetained, targetRetain, retaining⟩ := state.retainMany capturedRel retained
          obtain ⟨targetReleased, targetRelease, releasing⟩ :=
            retaining.releaseWork (.cons (.loc mapped) .nil) released
          have total : RValsIso (MapRel mapping) (captured ++ leftArguments).toList
              (targetCaptured ++ rightArguments).toList := by
            simpa only [Array.toList_append] using capturedRel.append arguments
          have supplied := values_extract total 0 arity
          have residual : RValsIso (MapRel mapping)
              ((captured ++ leftArguments).extract arity (captured ++ leftArguments).size).toList
              ((targetCaptured ++ rightArguments).extract arity
                (targetCaptured ++ rightArguments).size).toList := by
            simpa only [values_size total] using values_extract total arity (captured ++ leftArguments).size
          have empty : ((captured ++ leftArguments).extract arity (captured ++ leftArguments).size).isEmpty =
              ((targetCaptured ++ rightArguments).extract arity
                (targetCaptured ++ rightArguments).size).isEmpty := by
            simp only [Array.isEmpty, values_size residual]
          refine ⟨mapping, _, .papFn targetAt (boxes.world.symm.trans shared)
            targetNode (by rw [← values_size capturedRel]; exact capturedUnder)
            targetRetain targetRelease (by rw [← values_size total]; exact totalEnough)
            declaration papSafe (by rw [← values_size supplied]; exact suppliedArity) nonempty,
            ⟨releasing, MapExtends.refl _, rfl, .running (.entry definition supplied) (.cons ?_ stack)⟩⟩
          rw [empty]
          split
          · exact .resume resume
          · exact .applyMore resume residual
  | @papExtern location box address arity expectedArity captured retainedStore releasedStore remaining value
      found shared node capturedUnder retained released totalEnough declaration suppliedArity remainingEmpty called =>
      cases function with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetCaptured, targetAt, boxes, targetNode, capturedRel⟩ :=
            state.papView mapped found node
          obtain ⟨targetRetained, targetRetain, retaining⟩ := state.retainMany capturedRel retained
          obtain ⟨targetReleased, targetRelease, releasing⟩ :=
            retaining.releaseWork (.cons (.loc mapped) .nil) released
          have total : RValsIso (MapRel mapping) (captured ++ leftArguments).toList
              (targetCaptured ++ rightArguments).toList := by
            simpa only [Array.toList_append] using capturedRel.append arguments
          have supplied := values_extract total 0 arity
          have residual : RValsIso (MapRel mapping)
              ((captured ++ leftArguments).extract arity (captured ++ leftArguments).size).toList
              ((targetCaptured ++ rightArguments).extract arity
                (targetCaptured ++ rightArguments).size).toList := by
            simpa only [values_size total] using values_extract total arity (captured ++ leftArguments).size
          obtain ⟨targetCalled, valueRel⟩ := scalarOracle_related supplied called
          exact ⟨mapping, _, .papExtern targetAt (boxes.world.symm.trans shared)
            targetNode (by rw [← values_size capturedRel]; exact capturedUnder)
            targetRetain targetRelease (by rw [← values_size total]; exact totalEnough)
            declaration (by rw [← values_size supplied]; exact suppliedArity)
            (by simpa only [Array.isEmpty_iff_size_eq_zero, values_size residual] using remainingEmpty)
            targetCalled,
            ⟨releasing, MapExtends.refl _, rfl, .running (resume.push valueRel) stack⟩⟩

end Ix.Compiler.IxIR2.CreditRefinement
