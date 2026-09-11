import Ix.Compiler.IxIR2.CreditInstructions

/-! Jumps, dispatch, returns, and both tail-call forms. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)
open CallReuse.Sim (MapRel)

theorem terminator_related {context : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {heapFuel : Nat}
    {leftFrame rightFrame : Frame} {leftStack rightStack : List Continuation}
    {terminator : Terminator} {leftAfter : Machine}
    (state : HeapRel mapping leftStore rightStore)
    (frames : FrameRel mapping leftFrame rightFrame)
    (stack : StackRel mapping leftStack rightStack)
    (classified : TerminatorTransferCase context .logical leftStore heapFuel leftFrame
      leftStack terminator leftAfter) :
    ∃ after rightAfter,
      TerminatorTransferCase context .physical rightStore heapFuel rightFrame
        rightStack terminator rightAfter ∧ TransferRel mapping after leftAfter rightAfter := by
  cases classified with
  | jump transferred =>
      obtain ⟨target, targetTransfer, nextRel⟩ := frames.edge .nil transferred
      exact ⟨mapping, _, .jump targetTransfer,
        ⟨state, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  | switchCtor resolved boxAt node alternativeAt transferred =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      cases valueRel with
      | @loc _ targetLocation mapped =>
          obtain ⟨targetBox, targetFields, targetView, boxes, fieldsRel⟩ :=
            state.heap.constructorView mapped (ConstructorView.of_box boxAt rfl node)
          obtain ⟨target, targetTransfer, nextRel⟩ := frames.edge .nil transferred
          exact ⟨mapping, _, .switchCtor targetResolved targetView.parts.1 targetView.parts.2.2
            alternativeAt targetTransfer,
            ⟨state, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  | switchNatZero resolved transferred =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      cases valueRel
      obtain ⟨target, targetTransfer, nextRel⟩ := frames.edge .nil transferred
      exact ⟨mapping, _, .switchNatZero targetResolved targetTransfer,
        ⟨state, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  | switchNatSucc resolved transferred =>
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      cases valueRel
      obtain ⟨target, targetTransfer, nextRel⟩ := frames.edge (.cons .lit .nil) transferred
      exact ⟨mapping, _, .switchNatSucc targetResolved targetTransfer,
        ⟨state, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  | branchPresent lookedUp present transferred =>
      obtain ⟨targetCredit, targetLookup, creditRel⟩ := frames.creditLookup lookedUp
      obtain ⟨target, targetTransfer, nextRel⟩ := frames.edge .nil transferred
      exact ⟨mapping, _, .branchPresent targetLookup (creditRel.isPresent.symm.trans present) targetTransfer,
        ⟨state, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  | branchAbsent lookedUp absent transferred =>
      obtain ⟨targetCredit, targetLookup, creditRel⟩ := frames.creditLookup lookedUp
      obtain ⟨target, targetTransfer, nextRel⟩ := frames.edge .nil transferred
      exact ⟨mapping, _, .branchAbsent targetLookup (creditRel.isPresent.symm.trans absent) targetTransfer,
        ⟨state, MapExtends.refl _, rfl, .running nextRel stack⟩⟩
  | retResume resolved noCredits world =>
      cases stack with
      | cons head rest =>
          cases head with
          | resume caller =>
              obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
              exact ⟨mapping, _, .retResume targetResolved (frames.noCredits noCredits)
                (by rw [← frames.definition]; exact state.heap.hasWorld valueRel world),
                ⟨state, MapExtends.refl _, rfl, .running (caller.push valueRel) rest⟩⟩
  | retHalt resolved noCredits world =>
      cases stack
      obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
      exact ⟨mapping, _, .retHalt targetResolved (frames.noCredits noCredits)
        (by rw [← frames.definition]; exact state.heap.hasWorld valueRel world),
        ⟨state, MapExtends.refl _, rfl, .halted valueRel⟩⟩
  | retApplyMore resolved noCredits world transferred =>
      cases stack with
      | cons head rest =>
          cases head with
          | applyMore caller arguments =>
              obtain ⟨targetValue, targetResolved, valueRel⟩ := ReuseSim.resolveAtom_iso frames.values resolved
              obtain ⟨after, target, targetTransfer, related⟩ :=
                apply_related state valueRel arguments caller rest transferred
              exact ⟨after, target, .retApplyMore targetResolved (frames.noCredits noCredits)
                (by rw [← frames.definition]; exact state.heap.hasWorld valueRel world) targetTransfer, related⟩
  | tailCallFn noCredits resolved declaration arity nonempty =>
      obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
      exact ⟨mapping, _, .tailCallFn (frames.noCredits noCredits) targetResolved declaration
        (by rw [← values_size argumentsRel]; exact arity) nonempty,
        ⟨state, MapExtends.refl _, rfl, .running (.entry _ argumentsRel) stack⟩⟩
  | tailCallSelf noCredits resolved arity nonempty =>
      obtain ⟨targetArguments, targetResolved, argumentsRel⟩ := ReuseSim.resolveAtoms_iso frames.values resolved
      refine ⟨mapping, _, .tailCallSelf (frames.noCredits noCredits) targetResolved
        (by rw [← values_size argumentsRel, ← frames.definition]; exact arity)
        (by rw [← frames.definition]; exact nonempty),
        ⟨state, MapExtends.refl _, rfl, .running ?_ stack⟩⟩
      simpa only [frames.definition] using FrameRel.entry leftFrame.definition argumentsRel

end Ix.Compiler.IxIR2.CreditRefinement
