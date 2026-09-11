import Ix.Compiler.IxIR2.CreditApply

/-! Every instruction of the logical/physical credit language. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)
open CallReuse.Sim (MapRel)

theorem instruction_related {context : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {heapFuel : Nat}
    {leftFrame rightFrame : Frame} {leftStack rightStack : List Continuation}
    {instruction : Instr} {leftAfter : Machine}
    (state : HeapRel mapping leftStore rightStore)
    (frames : FrameRel mapping leftFrame rightFrame)
    (stack : StackRel mapping leftStack rightStack)
    (owned : (Machine.mk rightStore 0 (.running rightFrame rightStack)).ReservationOwnership)
    (classified : InstructionTransferCase context .logical leftStore heapFuel leftFrame
      leftStack instruction leftAfter) :
    ∃ after rightAfter,
      InstructionTransferCase context .physical rightStore heapFuel rightFrame
        rightStack instruction rightAfter ∧ TransferRel mapping after leftAfter rightAfter := by
  have advanced := frames.advance
  cases classified
  case move atom value resolved =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    exact ⟨mapping, _, .move targetResolved,
      ⟨state, MapExtends.refl _, rfl, .running (advanced.push valueRel) stack⟩⟩
  case alloc world cid arguments schema values schemaAt resolved fields =>
    obtain ⟨targetValues, targetResolved, valuesRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    have allocating := state.alloc (world := world) (leftNode := .ctorN cid values) (.ctor valuesRel)
    have extension : MapExtends mapping (mapping.push rightStore.heap.nodes.size) :=
      MapExtends.push mapping rightStore.heap.nodes.size
    have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
        (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
      .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
    exact ⟨_, _, .alloc schemaAt targetResolved (state.fieldWorlds valuesRel fields),
      ⟨allocating, extension, rfl,
        .running ((advanced.mono extension).push valueRel) (stack.mono extension)⟩⟩
  case allocWithAbsent index credit world cid arguments schema values next
      schemaAt resolved fields taken layout absent =>
    obtain ⟨targetValues, targetResolved, valuesRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    obtain ⟨targetNext, targetCredit, targetTaken, nextRel, creditRel⟩ := advanced.creditTake taken
    cases creditRel with
    | present => cases absent
    | absent creditLayout =>
        have allocating := state.alloc (world := world) (leftNode := .ctorN cid values) (.ctor valuesRel)
        have extension : MapExtends mapping (mapping.push rightStore.heap.nodes.size) :=
          MapExtends.push mapping rightStore.heap.nodes.size
        have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
            (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
          .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
        exact ⟨_, _, .allocWithAbsent schemaAt targetResolved (state.fieldWorlds valuesRel fields)
          targetTaken layout rfl, ⟨allocating, extension, rfl,
            .running ((nextRel.mono extension).push valueRel) (stack.mono extension)⟩⟩
  case allocWithLogical index credit world cid arguments schema values next
      mode schemaAt resolved fields taken layout present =>
    obtain ⟨targetValues, targetResolved, valuesRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    obtain ⟨targetNext, targetCredit, targetTaken, nextRel, creditRel⟩ := advanced.creditTake taken
    cases creditRel with
    | absent => cases present
    | present creditLayout location =>
        have empty := reservedCredit (frame := { rightFrame with pc := rightFrame.pc + 1 })
          owned targetTaken rfl
        obtain ⟨output, reused⟩ : ∃ output,
            rightStore.reuseReservation location world (.ctorN cid targetValues)
              schema.fields.size = .ok output := by
          unfold Store.reuseReservation
          rw [empty]
          exact ⟨_, rfl⟩
        have allocating := state.reuse (leftNode := .ctorN cid values) (.ctor valuesRel) reused
        have extension : MapExtends mapping (mapping.push location) := MapExtends.push mapping location
        have valueRel : RValIso (MapRel (mapping.push location))
            (.loc leftStore.heap.nodes.size) (.loc location) :=
          .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
        exact ⟨_, _, .allocWithPhysical rfl schemaAt targetResolved (state.fieldWorlds valuesRel fields)
          targetTaken layout rfl reused, ⟨allocating, extension, rfl,
            .running ((nextRel.mono extension).push valueRel) (stack.mono extension)⟩⟩
  case allocWithPhysical => contradiction
  case discardAbsent index credit next taken absent =>
    obtain ⟨targetNext, targetCredit, targetTaken, nextRel, creditRel⟩ := advanced.creditTake taken
    cases creditRel with
    | present => cases absent
    | absent => exact ⟨mapping, _, .discardAbsent targetTaken rfl,
        ⟨state, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  case discardLogical index credit next mode taken present =>
    obtain ⟨targetNext, targetCredit, targetTaken, nextRel, creditRel⟩ := advanced.creditTake taken
    cases creditRel with
    | absent => cases present
    | present creditLayout location =>
        have empty := reservedCredit (frame := { rightFrame with pc := rightFrame.pc + 1 })
          owned targetTaken rfl
        obtain ⟨output, released⟩ : ∃ output,
            rightStore.releaseReservation location = .ok output := by
          unfold Store.releaseReservation
          rw [empty]
          exact ⟨_, rfl⟩
        exact ⟨mapping, _, .discardPhysical rfl targetTaken rfl released,
          ⟨state.discard released, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  case discardPhysical => contradiction
  case takeUniqueLogical atom cid schema location box fields mode schemaAt resolved viewed unitRC =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    cases valueRel with
    | @loc _ targetLocation mapped =>
        obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
          state.heap.constructorView mapped viewed
        exact ⟨mapping, _, .takeUniquePhysical rfl schemaAt targetResolved targetView
          (boxes.rc.symm.trans unitRC),
          ⟨state.reserve mapped viewed.parts.1, MapExtends.refl _, rfl,
            .running (advanced.appendCredit fieldsRel (.present schema.layout targetLocation)) stack⟩⟩
  case takeUniquePhysical => contradiction
  case resetSharedLogicalHot atom cid schema location box fields mode schemaAt resolved viewed unitRC =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    cases valueRel with
    | @loc _ targetLocation mapped =>
        obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
          state.heap.constructorView mapped viewed
        exact ⟨mapping, _, .resetSharedPhysicalHot rfl schemaAt targetResolved targetView
          (boxes.rc.symm.trans unitRC),
          ⟨(state.tickAttempt.reserve mapped viewed.parts.1).tickHot, MapExtends.refl _, rfl,
            .running (advanced.appendCredit fieldsRel (.present schema.layout targetLocation)) stack⟩⟩
  case resetSharedPhysicalHot => contradiction
  case resetSharedCold atom cid schema location box fields output schemaAt resolved viewed many retained =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    cases valueRel with
    | @loc _ targetLocation mapped =>
        obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
          state.heap.constructorView mapped viewed
        have changed := ((state.tickAttempt.setBox mapped viewed.parts.1
          (newLeft := { box with rc := box.rc - 1 })
          (newRight := { targetBox with rc := targetBox.rc - 1 })
          ⟨boxes.world, congrArg (· - 1) boxes.rc, boxes.node⟩
          (IxIR1.Reclamation.AllocationOrderInvariant.setRc state.ordered viewed.parts.1
            (newRc := box.rc - 1) (by omega))).rcTick).tickCold
        obtain ⟨targetOutput, targetRetained, heap⟩ := changed.retainMany fieldsRel retained
        exact ⟨mapping, _, .resetSharedCold schemaAt targetResolved targetView
          (by rw [← boxes.rc]; exact many) targetRetained,
          ⟨heap, MapExtends.refl _, rfl,
            .running (advanced.appendCredit fieldsRel (.absent schema.layout)) stack⟩⟩
  case retainShared atom value output resolved retained =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    obtain ⟨targetOutput, targetRun, heap⟩ := state.retain valueRel retained
    exact ⟨mapping, _, .retainShared targetResolved targetRun,
      ⟨heap, MapExtends.refl _, rfl, .running (advanced.push valueRel) stack⟩⟩
  case releaseShared atom value output remaining resolved released =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    obtain ⟨targetOutput, targetRun, heap⟩ := state.releaseWork (.cons valueRel .nil) released
    exact ⟨mapping, _, .releaseShared targetResolved targetRun,
      ⟨heap, MapExtends.refl _, rfl, .running advanced stack⟩⟩
  case dropUnique atom value output remaining resolved dropped =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    obtain ⟨targetOutput, targetRun, heap⟩ := state.dropWork (.cons valueRel .nil) dropped
    exact ⟨mapping, _, .dropUnique targetResolved targetRun,
      ⟨heap, MapExtends.refl _, rfl, .running advanced stack⟩⟩
  case freeUnique atom cid location box fields resolved viewed scalarFields =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    cases valueRel with
    | @loc _ targetLocation mapped =>
        obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
          state.heap.constructorView mapped viewed
        exact ⟨mapping, _, .freeUnique targetResolved targetView
          (by rw [← values_scalar fieldsRel]; exact scalarFields),
          ⟨state.kill mapped viewed.parts.1, MapExtends.refl _, rfl, .running advanced stack⟩⟩
  case fetch atom cid field location box fields value resolved boxAt node fieldAt =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    cases valueRel with
    | @loc _ targetLocation mapped =>
        obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
          state.heap.constructorView mapped (ConstructorView.of_box boxAt rfl node)
        obtain ⟨targetField, targetFieldAt, fieldRel⟩ := fieldsRel.get? (by simpa using fieldAt)
        exact ⟨mapping, _, .fetch targetResolved targetView.parts.1 targetView.parts.2.2
          (by simpa using targetFieldAt),
          ⟨state, MapExtends.refl _, rfl, .running (advanced.push fieldRel) stack⟩⟩
  case callFn address atoms arguments definition noCredits resolved declaration arity nonempty =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    exact ⟨mapping, _, .callFn (frames.noCredits noCredits) targetResolved declaration
      (by rw [← values_size argumentsRel]; exact arity) nonempty,
      ⟨state, MapExtends.refl _, rfl,
        .running (.entry definition argumentsRel) (.cons (.resume advanced) stack)⟩⟩
  case callSelf atoms arguments noCredits resolved arity nonempty =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    refine ⟨mapping, _, .callSelf (frames.noCredits noCredits) targetResolved
      (by rw [← values_size argumentsRel, ← frames.definition]; exact arity)
      (by rw [← frames.definition]; exact nonempty),
      ⟨state, MapExtends.refl _, rfl, .running ?_ (.cons (.resume advanced) stack)⟩⟩
    simpa only [frames.definition] using FrameRel.entry leftFrame.definition argumentsRel
  case pappFn address atoms arguments definition noCredits declaration papSafe resolved under =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    have allocating := state.alloc (world := .shared)
      (leftNode := .papN address definition.signature.params.size arguments) (.pap argumentsRel)
    have extension : MapExtends mapping (mapping.push rightStore.heap.nodes.size) :=
      MapExtends.push mapping rightStore.heap.nodes.size
    have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
        (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
      .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
    exact ⟨_, _, .pappFn (frames.noCredits noCredits) declaration papSafe targetResolved
      (by rw [← values_size argumentsRel]; exact under),
      ⟨allocating, extension, rfl,
        .running ((advanced.mono extension).push valueRel) (stack.mono extension)⟩⟩
  case pappExtern address atoms arguments arity noCredits declaration resolved under =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    have allocating := state.alloc (world := .shared)
      (leftNode := .papN address arity arguments) (.pap argumentsRel)
    have extension : MapExtends mapping (mapping.push rightStore.heap.nodes.size) :=
      MapExtends.push mapping rightStore.heap.nodes.size
    have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
        (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
      .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
    exact ⟨_, _, .pappExtern (frames.noCredits noCredits) declaration targetResolved
      (by rw [← values_size argumentsRel]; exact under),
      ⟨allocating, extension, rfl,
        .running ((advanced.mono extension).push valueRel) (stack.mono extension)⟩⟩
  case apply functionAtom argumentAtoms function arguments noCredits functionResolved argumentsResolved transferred =>
    obtain ⟨targetFunction, targetFunctionResolved, functionRel⟩ :=
      ReuseSim.resolveAtom_iso frames.values functionResolved
    obtain ⟨targetArguments, targetArgumentsResolved, argumentsRel⟩ :=
      ReuseSim.resolveAtoms_iso frames.values argumentsResolved
    obtain ⟨after, target, transfer, related⟩ :=
      apply_related state functionRel argumentsRel advanced stack transferred
    exact ⟨after, target, .apply (frames.noCredits noCredits)
      targetFunctionResolved targetArgumentsResolved transfer, related⟩
  case extern address atoms arguments arity value noCredits resolved declaration argumentArity called =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    obtain ⟨targetCalled, valueRel⟩ := scalarOracle_related argumentsRel called
    exact ⟨mapping, _, .extern (frames.noCredits noCredits) targetResolved declaration
      (by rw [← values_size argumentsRel]; exact argumentArity) targetCalled,
      ⟨state, MapExtends.refl _, rfl, .running (advanced.push valueRel) stack⟩⟩

end Ix.Compiler.IxIR2.CreditRefinement
