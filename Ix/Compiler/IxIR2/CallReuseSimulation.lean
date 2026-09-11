import Ix.Compiler.IxIR2.CallReuseProgress

/-! Whole finite executions of the actual checked block rewrite. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval

def Simulates (limits : Validate.Limits) (validation : Validate.Context)
    (leftContext rightContext : Context) (mapping : Array Nat)
    (left right final : Machine) : Prop :=
  ∃ after targetCount targetFinal,
    Policy.Steps .suspendedCallsV1 rightContext .physical targetCount right targetFinal ∧
    TransferRel limits validation leftContext mapping after left.store right.store final targetFinal

/-- The compiler trace reconstructs caller suspension, every callee operation,
the reset prefixes, and final credit consumption. No root-liveness or cost
premise is supplied at a synchronization point. -/
theorem simulate_to_halt {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat} {left right final : Machine} {count : Nat}
    (contexts : ContextRel limits validation leftContext rightContext)
    (readyContext : ContextReady leftContext) (schemas : leftContext.schemas = validation.schemas)
    (machines : MachineRel limits validation leftContext mapping left right)
    (steps : Eval.Steps leftContext .physical count left final)
    (halted : ∃ value, final.control = .halted value) :
    Simulates limits validation leftContext rightContext mapping left right final := by
  induction count using Nat.strongRecOn generalizing mapping left right with
  | ind count ih =>
      have completeSuffix : ∀ {middleCount targetCount : Nat} {nextMap : Array Nat}
          {leftMiddle rightMiddle : Machine}, middleCount < count →
          Eval.Steps leftContext .physical middleCount leftMiddle final →
          Policy.Steps .suspendedCallsV1 rightContext .physical targetCount right rightMiddle →
          TransferRel limits validation leftContext mapping nextMap left.store right.store leftMiddle rightMiddle →
          Simulates limits validation leftContext rightContext mapping left right final := by
        intro middleCount targetCount nextMap leftMiddle rightMiddle smaller tail targetPrefix transferred
        have nextMachines := transferred.machineRel
          (targetPrefix.reservationOwnership machines.reservations)
        obtain ⟨lastMap, lastCount, targetFinal, rest, related⟩ := ih middleCount smaller nextMachines tail
        exact ⟨lastMap, targetCount + lastCount, targetFinal, targetPrefix.trans rest,
          ⟨transferred.transition.trans related.transition, related.fuel, related.control⟩⟩
      rcases left with ⟨leftStore, leftFuel, leftControl⟩
      rcases right with ⟨rightStore, rightFuel, rightControl⟩
      cases machines.control with
      | halted values =>
          cases steps with
          | refl => exact ⟨mapping, 0, _, .refl _, ⟨.refl machines.heapState, machines.fuel, .halted values⟩⟩
          | cons running _ _ => cases running
      | @running block leftFrame rightFrame leftStack rightStack frames stack =>
          have ordinary : (leftFrame.pc ≠ 0 ∨ inspect limits validation block = none) →
              Simulates limits validation leftContext rightContext mapping
                { store := leftStore, heapFuel := leftFuel, control := .running leftFrame leftStack }
                { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } final := by
            intro outside
            cases steps with
            | refl => obtain ⟨value, impossible⟩ := halted; cases impossible
            | cons _ head tail =>
                obtain ⟨nextMap, target, targetStep, related⟩ :=
                  stable_step_related contexts readyContext schemas machines frames stack outside head
                exact completeSuffix (by omega) tail (.cons rfl targetStep (.refl _)) related
          by_cases zero : leftFrame.pc = 0
          · cases decideBlock limits validation block with
            | unchanged rejected => exact ordinary (.inr rejected)
            | accepted site produced =>
                obtain ⟨targetZero, targetCredits⟩ := frames.position.entry_parts produced zero
                have parameterCount : leftFrame.values.size = site.shape.valueParams.size := by
                  simpa only [site.exact, Shape.baseline] using frames.entryCount zero
                have canonical := Frame.entry_eq zero frames.leftCredits
                have canonicalSteps : Eval.Steps leftContext .physical count
                    { store := leftStore, heapFuel := leftFuel
                      control := .running
                        { definition := leftFrame.definition, block := leftFrame.block, values := leftFrame.values }
                        leftStack } final := by
                  simpa only [← canonical] using steps
                obtain ⟨location, box, fields, retained, released, remainingFuel, remainingCount,
                    resolved, found, shared, node, fieldCount, retains, releases, counts, tail⟩ :=
                  baseline_prefix_trace site frames.sourceAt parameterCount schemas machines.ordered
                    machines.shaped halted canonicalSteps
                rcases box with ⟨world, rc, payload⟩
                dsimp only at shared node
                subst world
                subst payload
                obtain ⟨target, targetPrefix, related⟩ := reset_prefix_related contexts schemas machines
                  frames stack produced zero targetZero targetCredits resolved found fieldCount retains releases
                apply completeSuffix (middleCount := remainingCount) (by omega) _ targetPrefix related
                simpa only [frames.leftCredits] using tail
          · exact ordinary (.inl zero)

end Ix.Compiler.IxIR2.CallReuse.Sim
