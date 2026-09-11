import Ix.Compiler.Recursion.Allocation
import Ix.Compiler.IxIR2.PipelineCosts

/-!
# Source refinement with RC and peak-live bounds

The source contracts and semantic relations remain those of D2, R2, and R3.
Recovered shared mains additionally bound selected RC work and every recorded
live-node peak by the actual physical baseline, including intermediate states
and complete shared-result reclamation. Literal fallback retains R3's endpoint.
-/

namespace Ix.Compiler.Recursion

open Ix.Compiler.Ixon (Address Constant)

namespace Lowered

variable {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
  {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}

/-- Successful source execution derives all compiler and heap invariants
internally, retaining the same selected semantic value and shared resources. -/
theorem physicalMainCostLaws (lowered : Lowered recovery fuel)
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    (sourceRun : IxIR0.eval lowered.compilation.sourceCtx sourceFuel []
      lowered.compilation.main = .ok sourceValue) :
    ∃ controlFuel heapFuel result,
      IxIR2.Eval.runMain
        (IxIR2.Eval.Context.ofProgram lowered.reuse.target
          lowered.attached.target.artifact.validationContext.schemas)
        .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
      lowered.PhysicalValueRel sourceValue result ∧ result.SharedResources ∧
      lowered.attached.CostComparison lowered.reuse heapFuel result := by
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
    lowered.attached.selectedPhysicalMainCostLaws lowered.reuse attachedRun
  exact ⟨controlFuel, heapFuel, result, run,
    ⟨store, value, baseline, locRel, ⟨rawStore, addressImage, graph⟩,
      baselineRelation, heaps, values⟩, resources,
    baselineControl, heapFuel, baseline, baselineRun, baselineResources,
    allocations, costs, reclaimed, prefixes⟩

end Lowered

namespace Compilation

variable {constants : List (Address × Constant)} {root : Address}
  {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}

/-- Recovered shared results carry the full comparison with an actual
physical baseline. Both selection branches have RC and peak bounds; literal
fallback retains exactly the existing allocation/resource endpoint. -/
def SelectedExecutionWithCostLaws
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) : Prop :=
  match compilation.outcome with
  | .literal _ => compilation.SelectedExecutionWithAllocationLaws sourceValue
  | .recovered _ lowered =>
      ∃ rawValue controlFuel heapFuel result,
        compilation.SourceValueRel sourceValue rawValue ∧
        IxIR2.Eval.runMain
          (IxIR2.Eval.Context.ofProgram lowered.reuse.target
            lowered.attached.target.artifact.validationContext.schemas)
          .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
        lowered.PhysicalValueRel rawValue result ∧ result.SharedResources ∧
        lowered.attached.CostComparison lowered.reuse heapFuel result

/-- Forgetting the new bounds recovers R3's unchanged source endpoint. -/
theorem SelectedExecutionWithCostLaws.allocations
    {compilation : Compilation constants root config eraseFuel lowerFuel}
    {sourceValue : Ixon.Eval.Value}
    (execution : compilation.SelectedExecutionWithCostLaws sourceValue) :
    compilation.SelectedExecutionWithAllocationLaws sourceValue := by
  cases selected : compilation.outcome with
  | literal reason => simpa only [SelectedExecutionWithCostLaws, selected] using execution
  | recovered recovery lowered =>
      simp only [SelectedExecutionWithCostLaws, SelectedExecutionWithAllocationLaws,
        selected] at execution ⊢
      obtain ⟨raw, control, heap, result, source, run, relation, resources, costs⟩ := execution
      exact ⟨raw, control, heap, result, source, run, relation, resources, costs.allocations⟩

/-- Source refinement with allocation/free laws, RC and peak bounds, and
complete reclamation, under exactly the original source sharing and oracle
contracts. Compiler trace invariants and both selection branches are internal. -/
theorem sourceRefinesSelectedWithCostLaws
    (compilation : Compilation constants root config eraseFuel lowerFuel)
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
        compilation.sourceRefinesSelectedWithAllocationLaws horacles hctx hsource
  | recovered recovery lowered =>
      obtain ⟨rawFuel, rawValue, rawRun, sourceRelation⟩ := compilation.sourceRefines horacles hctx hsource
      rw [selected] at rawRun
      obtain ⟨controlFuel, heapFuel, result, run, relation, resources, costs⟩ :=
        lowered.physicalMainCostLaws rawRun
      simp only [SelectedExecutionWithCostLaws, selected]
      exact ⟨rawValue, controlFuel, heapFuel, result, sourceRelation, run, relation, resources, costs⟩

end Compilation

end Ix.Compiler.Recursion
