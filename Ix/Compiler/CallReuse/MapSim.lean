import Ix.Compiler.CallReuse.MapPipeline
import Ix.Compiler.IxIR0.MapRecoverySim
import Ix.Compiler.Recursion.Resources
import Ix.Compiler.IxIR2.PipelineCallReuse

/-! The valid Ixon map, exact checked specialization, ordinary ownership
lowering, and selected call-credit execution compose with the original source
contracts. Optional specialization/backend failure retains literal owned
execution and reclamation; successful attachment carries all R4 cost laws. -/

namespace Ix.Compiler.CallReuse

open Ix.Compiler.Ixon (Address Constant)

namespace MapLowered

variable {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
  {recovery : IxIR0.MapRecovery.Recovered declarations main} {fuel : Nat}

def PhysicalValueRel (lowered : MapLowered recovery fuel) (sourceValue : IxIR0.Value)
    (result : IxIR2.Eval.Result) : Prop :=
  ∃ store value baseline locRel,
    IxIR1.LowerSim.AddressedValueGraph
      (lowered.lowering.result.rebuildRename lowered.lowering.raw)
      lowered.compilation.functionRel store sourceValue value ∧
    IxIR2.Lower.Sim.OutcomeRel (store, value) baseline ∧
    IxIR2.ReuseSim.StableHeapRel baseline.store result.store locRel ∧
    IxIR1.Sim.RValIso locRel baseline.value result.value

theorem physicalMainCostLaws (lowered : MapLowered recovery fuel)
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    (sourceRun : IxIR0.eval lowered.compilation.sourceCtx sourceFuel []
      lowered.compilation.main = .ok sourceValue) :
    ∃ controlFuel heapFuel result,
      IxIR2.Eval.Policy.runMain lowered.reuse.policy
        (IxIR2.Eval.Context.ofProgram lowered.reuse.target lowered.attached.target.artifact.validationContext.schemas)
        .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
      lowered.PhysicalValueRel sourceValue result ∧ result.SharedResources ∧
      lowered.attached.CallCostComparison lowered.reuse heapFuel result := by
  have trace : IxIR0.ProjectionSafe.Eval lowered.compilation.sourceCtx sourceFuel []
      lowered.compilation.main sourceValue := recovery.projectionSafe sourceRun
  obtain ⟨ir1Fuel, rawStore, store, value, ownedRun, addressImage, graph⟩ :=
    lowered.compilation.addressedOwnedMain trace
  have attachedRun : IxIR1.runOwnedMain lowered.attached.simulationSourceContext
      lowered.attached.target.artifact.source.mainResult
      lowered.attached.target.artifact.source.main ir1Fuel = .ok (store, value) := by
    rw [lowered.attached.simulationSourceContext_eq_addressedCtx,
      lowered.attached.targetSourceProduced, lowered.attached.inputProduced, lowered.sourceProduced]
    exact ownedRun
  obtain ⟨baselineControl, controlFuel, heapFuel, baseline, result, locRel,
      baselineRun, run, baselineRelation, heaps, values, baselineResources, resources,
      allocations, costs, reclaimed, prefixes⟩ :=
    lowered.attached.selectedCallPhysicalMainCostLaws lowered.reuse attachedRun
  exact ⟨controlFuel, heapFuel, result, run,
    ⟨store, value, baseline, locRel, ⟨rawStore, addressImage, graph⟩, baselineRelation, heaps, values⟩,
    resources, baselineControl, heapFuel, baseline, baselineRun, baselineResources,
    allocations, costs, reclaimed, prefixes⟩

end MapLowered

namespace MapCompilation

variable {constants : List (Address × Constant)} {root : Address}
  {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}

/-- A proof-only view reuses the established literal source/owned endpoint.
It contains the same validated compilation and performs no transformation. -/
def literalView (compilation : MapCompilation constants root config eraseFuel lowerFuel) :
    Recursion.Compilation constants root config eraseFuel lowerFuel :=
  { source := compilation.source, outcome := .literal (.recovery .unrecognized) }

abbrev SourceValueRel (compilation : MapCompilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) (rawValue : IxIR0.Value) : Prop :=
  compilation.literalView.SourceValueRel sourceValue rawValue

theorem sourceRefines (compilation : MapCompilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    ∃ targetFuel rawValue,
      IxIR0.eval { env := IxIR0.Env.ofList compilation.outcome.selected.declarations }
        targetFuel [] compilation.outcome.selected.main = .ok rawValue ∧
      compilation.SourceValueRel sourceValue rawValue := by
  obtain ⟨rawFuel, rawValue, rawRun, sourceRelation⟩ := compilation.literalView.sourceRefines horacles hctx hsource
  obtain ⟨targetFuel, targetRun⟩ := compilation.outcome.selected.forwardSimulation rawRun
  exact ⟨targetFuel, rawValue, targetRun, sourceRelation⟩

def SelectedExecutionWithCostLaws (compilation : MapCompilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) : Prop :=
  match compilation.outcome with
  | .literal _ => compilation.literalView.SelectedExecutionWithResources sourceValue
  | .recovered _ lowered =>
      ∃ rawValue controlFuel heapFuel result,
        compilation.SourceValueRel sourceValue rawValue ∧
        IxIR2.Eval.Policy.runMain lowered.reuse.policy
          (IxIR2.Eval.Context.ofProgram lowered.reuse.target lowered.attached.target.artifact.validationContext.schemas)
          .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
        lowered.PhysicalValueRel rawValue result ∧ result.SharedResources ∧
        lowered.attached.CallCostComparison lowered.reuse heapFuel result

/-- Composed source correctness, checked fallback, full result reclamation,
and allocation/free/RC/peak laws. The only caller premises are the original
source sharing/oracle contracts and successful Ixon evaluation. -/
theorem sourceRefinesWithCostLaws (compilation : MapCompilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    compilation.SelectedExecutionWithCostLaws sourceValue := by
  cases selected : compilation.outcome with
  | literal reason =>
      simpa only [SelectedExecutionWithCostLaws, selected] using
        compilation.literalView.sourceRefinesSelectedWithResources horacles hctx hsource
  | recovered recovery lowered =>
      obtain ⟨rawFuel, rawValue, rawRun, sourceRelation⟩ := compilation.sourceRefines horacles hctx hsource
      rw [selected] at rawRun
      obtain ⟨controlFuel, heapFuel, result, run, related, resources, costs⟩ := lowered.physicalMainCostLaws rawRun
      simp only [SelectedExecutionWithCostLaws, selected]
      exact ⟨rawValue, controlFuel, heapFuel, result, sourceRelation, run, related, resources, costs⟩

end MapCompilation

end Ix.Compiler.CallReuse
