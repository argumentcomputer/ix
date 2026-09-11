import Ix.Compiler.Recursion.Resources
import Ix.Compiler.IxIR2.PipelineAllocation

/-!
# Source refinement with comparative allocation laws

The source contracts and semantic relations remain those of D2 and R2.
Recovered shared-main execution additionally compares the actual selected
physical result with an actual checked baseline run, before and after shared
reclamation. Literal fallback retains R2's original owned execution.
-/

namespace Ix.Compiler.Recursion

open Ix.Compiler.Ixon (Address Constant)

namespace Lowered

variable {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
  {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}

/-- Source execution derives every backend premise and produces the same
selected semantic result, its R2 resources, and comparison with an actual
physical baseline. -/
theorem physicalMainAllocationLaws (lowered : Lowered recovery fuel)
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    (sourceRun : IxIR0.eval lowered.compilation.sourceCtx sourceFuel []
      lowered.compilation.main = .ok sourceValue) :
    ∃ controlFuel heapFuel result,
      IxIR2.Eval.runMain
        (IxIR2.Eval.Context.ofProgram lowered.reuse.target
          lowered.attached.target.artifact.validationContext.schemas)
        .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
      lowered.PhysicalValueRel sourceValue result ∧ result.SharedResources ∧
      lowered.attached.AllocationComparison result := by
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
      laws, reclaimed⟩ :=
    lowered.attached.selectedPhysicalMainAllocationLaws lowered.reuse attachedRun
  exact ⟨controlFuel, heapFuel, result, run,
    ⟨store, value, baseline, locRel, ⟨rawStore, addressImage, graph⟩,
      baselineRelation, heaps, values⟩, resources,
    baselineControl, heapFuel, baseline, baselineRun, baselineResources, laws, reclaimed⟩

end Lowered

namespace Compilation

variable {constants : List (Address × Constant)} {root : Address}
  {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}

/-- Recovered shared results carry comparative allocation/free laws for
actual baseline and selected runs. Literal fallback keeps exactly R2's
resource endpoint. -/
def SelectedExecutionWithAllocationLaws
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) : Prop :=
  match compilation.outcome with
  | .literal _ => compilation.SelectedExecutionWithResources sourceValue
  | .recovered _ lowered =>
      ∃ rawValue controlFuel heapFuel result,
        compilation.SourceValueRel sourceValue rawValue ∧
        IxIR2.Eval.runMain
          (IxIR2.Eval.Context.ofProgram lowered.reuse.target
            lowered.attached.target.artifact.validationContext.schemas)
          .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
        lowered.PhysicalValueRel rawValue result ∧ result.SharedResources ∧
        lowered.attached.AllocationComparison result

/-- Forgetting comparative evidence recovers the unchanged R2 endpoint. -/
theorem SelectedExecutionWithAllocationLaws.resources
    {compilation : Compilation constants root config eraseFuel lowerFuel}
    {sourceValue : Ixon.Eval.Value}
    (execution : compilation.SelectedExecutionWithAllocationLaws sourceValue) :
    compilation.SelectedExecutionWithResources sourceValue := by
  cases selected : compilation.outcome with
  | literal reason =>
      simpa only [SelectedExecutionWithAllocationLaws, selected] using execution
  | recovered recovery lowered =>
      simp only [SelectedExecutionWithAllocationLaws, SelectedExecutionWithResources,
        selected] at execution ⊢
      obtain ⟨raw, control, heap, result, source, run, relation, resources, _laws⟩ := execution
      exact ⟨raw, control, heap, result, source, run, relation, resources⟩

/-- Successful source evaluation supplies the selected execution and the
comparative laws with exactly the original sharing and oracle contracts.
The recovered branch covers both optimized and checked baseline selection. -/
theorem sourceRefinesSelectedWithAllocationLaws
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    compilation.SelectedExecutionWithAllocationLaws sourceValue := by
  cases selected : compilation.outcome with
  | literal reason =>
      simpa only [SelectedExecutionWithAllocationLaws, selected] using
        compilation.sourceRefinesSelectedWithResources horacles hctx hsource
  | recovered recovery lowered =>
      obtain ⟨rawFuel, rawValue, rawRun, sourceRelation⟩ :=
        compilation.sourceRefines horacles hctx hsource
      rw [selected] at rawRun
      obtain ⟨controlFuel, heapFuel, result, run, relation, resources, laws⟩ :=
        lowered.physicalMainAllocationLaws rawRun
      simp only [SelectedExecutionWithAllocationLaws, selected]
      exact ⟨rawValue, controlFuel, heapFuel, result, sourceRelation, run, relation, resources, laws⟩

end Compilation

end Ix.Compiler.Recursion
