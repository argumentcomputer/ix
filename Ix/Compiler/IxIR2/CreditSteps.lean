import Ix.Compiler.IxIR2.CreditTerminators

/-! The complete small-step bridge, including continuation-owned v1 credits. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval

theorem original_step_related {context : Context} {mapping : Array Nat}
    {left right leftAfter : Machine} (machines : MachineRel mapping left right)
    (stepped : Eval.Step context .logical left leftAfter) :
    ∃ after rightAfter, Eval.Step context .physical right rightAfter ∧
      TransferRel mapping after leftAfter rightAfter := by
  rcases left with ⟨leftStore, leftFuel, leftControl⟩
  rcases right with ⟨rightStore, rightFuel, rightControl⟩
  have fuels := machines.fuel
  dsimp only at fuels
  subst rightFuel
  cases machines.control with
  | halted values =>
      have same := Except.ok.inj stepped
      subst leftAfter
      exact ⟨mapping, _, rfl,
        ⟨machines.heap, MapExtends.refl _, rfl, .halted values⟩⟩
  | running frames stack =>
      cases stepped.classify with
      | instruction blockAt pc instructionAt classified =>
          obtain ⟨after, target, targetCase, related⟩ :=
            instruction_related machines.heap frames stack machines.reservations classified
          exact ⟨after, target, targetCase.step
            (by rw [← frames.definition, ← frames.block]; exact blockAt)
            (by rw [← frames.pc]; exact pc)
            (by simpa only [← frames.pc] using instructionAt), related⟩
      | terminator blockAt pc terminatorAt classified =>
          obtain ⟨after, target, targetCase, related⟩ :=
            terminator_related machines.heap frames stack classified
          exact ⟨after, target, targetCase.step
            (by rw [← frames.definition, ← frames.block]; exact blockAt)
            (by rw [← frames.pc]; exact pc) terminatorAt, related⟩

theorem FrameRel.directCall {mapping : Array Nat} {left right : Frame}
    (frames : FrameRel mapping left right) : Policy.directCall? left = Policy.directCall? right := by
  unfold Policy.directCall?
  rw [frames.definition, frames.block, frames.pc]

theorem FrameRel.callDefinition {mapping : Array Nat} {left right : Frame}
    (frames : FrameRel mapping left right) (context : Context) (call : Policy.DirectCall) :
    call.definition context left = call.definition context right := by
  cases call with
  | function => rfl
  | self => simp only [Policy.DirectCall.definition, frames.definition]

theorem step_related {policy : CreditPolicy} {context : Context} {mapping : Array Nat}
    {left right leftAfter : Machine} (machines : MachineRel mapping left right)
    (stepped : Policy.Step policy context .logical left leftAfter) :
    ∃ after rightAfter, Policy.Step policy context .physical right rightAfter ∧
      TransferRel mapping after leftAfter rightAfter := by
  rcases stepped.classify with original | ⟨frame, stack, call, rfl, running, atCall, called⟩
  · obtain ⟨after, target, targetStep, related⟩ := original_step_related machines original
    refine ⟨after, target, ?_, related⟩
    cases policy with
    | callLocalV0 => exact targetStep
    | suspendedCallsV1 => exact Policy.of_originalStep targetStep
  · rcases left with ⟨leftStore, leftFuel, leftControl⟩
    rcases right with ⟨rightStore, rightFuel, rightControl⟩
    dsimp only at running
    subst leftControl
    have controls := machines.control
    dsimp only at controls
    cases controls with
    | @running _ rightFrame _ rightStack frames stacks =>
        obtain ⟨values, definition, resolved, defined, arity, nonempty, rfl⟩ :=
          Policy.suspendCall_iff.mp called
        obtain ⟨targetValues, targetResolved, valuesRel⟩ :=
          ReuseSim.resolveAtoms_iso frames.values resolved
        have targetAt : Policy.directCall? rightFrame = some call :=
          frames.directCall.symm.trans atCall
        have targetCall := (Policy.suspendCall_iff
          (machine := Machine.mk rightStore rightFuel (.running rightFrame rightStack))
          (frame := rightFrame) (stack := rightStack) (call := call)).mpr
          ⟨targetValues, definition, targetResolved,
            (frames.callDefinition context call).symm.trans defined,
            (values_size valuesRel).symm.trans arity, nonempty, rfl⟩
        refine ⟨mapping, Machine.mk rightStore rightFuel
          (.running { definition, values := targetValues }
            (.resume { rightFrame with pc := rightFrame.pc + 1 } :: rightStack)), ?_,
          ⟨machines.heap, MapExtends.refl _, machines.fuel,
            .running (.entry definition valuesRel) (.cons (.resume frames.advance) stacks)⟩⟩
        simpa only [Policy.Step, Policy.step, targetAt] using targetCall

/-- Every finite logical prefix has a physical prefix of the same length,
with equal remaining heap fuel, exact observation agreement, and unique
reservations across all active and suspended frames. -/
theorem steps_related {policy : CreditPolicy} {context : Context} {mapping : Array Nat}
    {left right leftAfter : Machine} {count : Nat}
    (machines : MachineRel mapping left right)
    (steps : Policy.Steps policy context .logical count left leftAfter) :
    ∃ after rightAfter, Policy.Steps policy context .physical count right rightAfter ∧
      MachineRel after leftAfter rightAfter ∧ MapExtends mapping after := by
  induction steps generalizing mapping right with
  | refl => exact ⟨mapping, right, .refl _, machines, MapExtends.refl _⟩
  | @cons count left middle final frame stack running head tail ih =>
      obtain ⟨middleMap, targetMiddle, targetHead, transferred⟩ := step_related machines head
      have next := transferred.machine (targetHead.reservationOwnership machines.reservations)
      obtain ⟨after, target, targetTail, related, extension⟩ := ih next
      rcases right with ⟨rightStore, rightFuel, rightControl⟩
      have controls := machines.control
      rw [running] at controls
      cases controls with
      | running frames stacks =>
          exact ⟨after, target, .cons rfl targetHead targetTail, related,
            MapExtends.trans transferred.extension extension⟩

theorem initial_related (definition : Function) (heapFuel : Nat) :
    MachineRel #[] (initialMachine definition #[] heapFuel)
      (initialMachine definition #[] heapFuel) :=
  ⟨.empty, rfl, .running (.entry definition .nil) .nil,
    Policy.initialMachine_reservationOwnership ..⟩

end Ix.Compiler.IxIR2.CreditRefinement
