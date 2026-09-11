import Ix.Compiler.IxIR2.CallReuseApply

/-! Forward simulation of every ordinary instruction in an unchanged block. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)

theorem values_scalar {mapping : Array Nat} {left right : Array RVal}
    (related : RValsIso (MapRel mapping) left.toList right.toList) :
    left.all RVal.isScalar = right.all RVal.isScalar := by
  rw [← Array.all_toList, ← Array.all_toList]
  generalize left.toList = leftList at related ⊢
  generalize right.toList = rightList at related ⊢
  induction related with
  | nil => rfl
  | cons head tail ih => cases head <;> simp only [List.all_cons, RVal.isScalar, ih]

theorem instruction_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat}
    {block : Block} {leftFrame rightFrame : Frame} {leftStack rightStack : List Continuation}
    {instruction : Instr} {leftAfter : Machine}
    (contexts : ContextRel limits validation leftContext rightContext)
    (readyContext : ContextReady leftContext)
    (state : HeapState leftContext mapping leftStore rightStore) (fuel : leftFuel ≤ rightFuel)
    (frames : FrameRel limits validation mapping block leftFrame rightFrame)
    (stack : StackRel limits validation mapping leftStack rightStack)
    (rejected : inspect limits validation block = none)
    (free : CreditFree.instruction instruction = true)
    (classified : InstructionTransferCase leftContext .physical leftStore leftFuel leftFrame
      leftStack instruction leftAfter) :
    ∃ after rightAfter,
      InstructionTransferCase rightContext .physical rightStore rightFuel rightFrame
        rightStack instruction rightAfter ∧
      TransferRel limits validation leftContext mapping after leftStore rightStore leftAfter rightAfter := by
  have advanced := frames.advanceUnchanged rejected
  have positive : 0 < ({ leftFrame with pc := leftFrame.pc + 1 } : Frame).pc := by simp
  have cleared := (frames.unchanged rejected).2
  cases classified <;> try simp only [CreditFree.instruction, Bool.false_eq_true] at free
  case move atom value resolved =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    exact ⟨mapping, _, .move targetResolved,
      ⟨.refl state, fuel, .running (advanced.pushResult positive valueRel) stack⟩⟩
  case alloc world cid arguments schema values schemaAt resolved fields =>
    obtain ⟨targetValues, targetResolved, valuesRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    have allocating := state.alloc (world := world) (leftNode := .ctorN cid values)
      (.ctor valuesRel) ⟨schema, schemaAt, fields.size⟩
    have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
        (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
      .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
    exact ⟨_, _, .alloc (by rw [← contexts.schemas]; exact schemaAt)
      targetResolved (state.heap.fieldWorlds valuesRel fields),
      ⟨allocating, fuel, .running ((advanced.mono allocating.extension).pushResult positive valueRel)
        (stack.mono allocating.extension)⟩⟩
  case retainShared atom value output resolved retained =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    obtain ⟨targetOutput, targetRetain, retaining⟩ := state.retain valueRel retained
    exact ⟨mapping, _, .retainShared targetResolved targetRetain,
      ⟨retaining, fuel, .running (advanced.pushResult positive valueRel) stack⟩⟩
  case releaseShared atom value output remaining resolved released =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    obtain ⟨targetOutput, targetFuel, targetRelease, remainingFuel, releasing⟩ :=
      state.releaseWork fuel (.cons valueRel .nil) released
    exact ⟨mapping, _, .releaseShared targetResolved targetRelease,
      ⟨releasing, remainingFuel, .running advanced stack⟩⟩
  case dropUnique atom value output remaining resolved dropped =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    obtain ⟨targetOutput, targetFuel, targetDrop, remainingFuel, dropping⟩ :=
      state.dropWork fuel (.cons valueRel .nil) dropped
    exact ⟨mapping, _, .dropUnique targetResolved targetDrop,
      ⟨dropping, remainingFuel, .running advanced stack⟩⟩
  case freeUnique atom cid location box fields resolved viewed scalarFields =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    cases valueRel with
    | @loc _ targetLocation mapped =>
        obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
          state.heap.constructorView mapped viewed
        exact ⟨mapping, _, .freeUnique targetResolved targetView
          (by rw [← values_scalar fieldsRel]; exact scalarFields),
          ⟨state.freeUnique mapped viewed.parts.1, fuel, .running advanced stack⟩⟩
  case fetch atom cid field location box fields value resolved boxAt node fieldAt =>
    obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
    cases valueRel with
    | @loc _ targetLocation mapped =>
        obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
          state.heap.constructorView mapped (ConstructorView.of_box boxAt rfl node)
        obtain ⟨targetField, targetFieldAt, fieldRel⟩ := fieldsRel.get? (by simpa using fieldAt)
        exact ⟨mapping, _, .fetch targetResolved targetView.parts.1 targetView.parts.2.2
          (by simpa using targetFieldAt),
          ⟨.refl state, fuel, .running (advanced.pushResult positive fieldRel) stack⟩⟩
  case callFn address atoms arguments definition noCredits resolved declaration arity nonempty =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    obtain ⟨entryBlock, entry⟩ := FrameRel.functionEntry (limits := limits)
      (validation := validation) (readyContext declaration) argumentsRel arity
    exact ⟨mapping, _, .callFn cleared targetResolved (contexts.function declaration)
      (by simpa only [rewriteFunction_signature, ← values_size argumentsRel] using arity)
      (rewriteFunction_nonempty nonempty),
      ⟨.refl state, fuel, .running entry (.cons (.resume advanced positive) stack)⟩⟩
  case callSelf atoms arguments noCredits resolved arity nonempty =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    obtain ⟨entryBlock, entry⟩ := FrameRel.functionEntry (limits := limits)
      (validation := validation) frames.ready argumentsRel arity
    have targetArity : targetArguments.size = rightFrame.definition.signature.params.size := by
      simpa only [frames.definition, rewriteFunction_signature, ← values_size argumentsRel] using arity
    have targetNonempty : rightFrame.definition.blocks.isEmpty = false := by
      simpa only [frames.definition] using rewriteFunction_nonempty (limits := limits)
        (context := validation) nonempty
    refine ⟨mapping, _, .callSelf cleared targetResolved targetArity targetNonempty,
      ⟨.refl state, fuel, .running (sourceBlock := entryBlock) ?_
        (.cons (.resume advanced positive) stack)⟩⟩
    simpa only [frames.definition] using entry
  case pappFn address atoms arguments definition noCredits declaration papSafe resolved under =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    have allocating := state.alloc (world := .shared)
      (leftNode := .papN address definition.signature.params.size arguments) (.pap argumentsRel) trivial
    have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
        (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
      .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
    exact ⟨_, _, .pappFn cleared (contexts.function declaration) papSafe targetResolved
      (by simpa only [rewriteFunction_signature, ← values_size argumentsRel] using under),
      ⟨allocating, fuel, .running ((advanced.mono allocating.extension).pushResult positive valueRel)
        (stack.mono allocating.extension)⟩⟩
  case pappExtern address atoms arguments arity noCredits declaration resolved under =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    have allocating := state.alloc (world := .shared)
      (leftNode := .papN address arity arguments) (.pap argumentsRel) trivial
    have valueRel : RValIso (MapRel (mapping.push rightStore.heap.nodes.size))
        (.loc leftStore.heap.nodes.size) (.loc rightStore.heap.nodes.size) :=
      .loc (by rw [← state.heap.size]; exact MapRel.fresh ..)
    exact ⟨_, _, .pappExtern cleared (contexts.extern declaration) targetResolved
      (by rw [← values_size argumentsRel]; exact under),
      ⟨allocating, fuel, .running ((advanced.mono allocating.extension).pushResult positive valueRel)
        (stack.mono allocating.extension)⟩⟩
  case apply functionAtom argumentAtoms function arguments noCredits functionResolved argumentsResolved transferred =>
    obtain ⟨targetFunction, targetFunctionResolved, functionRel⟩ :=
      ReuseSim.resolveAtom_iso frames.values functionResolved
    obtain ⟨targetArguments, targetArgumentsResolved, argumentsRel⟩ :=
      ReuseSim.resolveAtoms_iso frames.values argumentsResolved
    obtain ⟨after, target, transfer, related⟩ := apply_related contexts readyContext state fuel
      functionRel argumentsRel advanced positive stack transferred
    exact ⟨after, target, .apply cleared targetFunctionResolved targetArgumentsResolved transfer, related⟩
  case extern address atoms arguments arity value noCredits resolved declaration argumentArity called =>
    obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
    obtain ⟨targetCalled, valueRel⟩ := scalarOracle_related contexts argumentsRel called
    exact ⟨mapping, _, .extern cleared targetResolved (contexts.extern declaration)
      (by rw [← values_size argumentsRel]; exact argumentArity) targetCalled,
      ⟨.refl state, fuel, .running (advanced.pushResult positive valueRel) stack⟩⟩

end Ix.Compiler.IxIR2.CallReuse.Sim
