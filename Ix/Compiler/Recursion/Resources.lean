import Ix.Compiler.Recursion.PhysicalSim
import Ix.Compiler.IxIR2.PipelineResources

/-!
# Source refinement with terminal resources

The source contracts are exactly those of D2. Each successful selected target
execution preserves the existing value relation, accounts for all physical
reservations at halt, and admits complete reclamation of its shared result.
Literal fallback retains the original owned IxIR₁ execution and its release.
-/

namespace Ix.Compiler.Recursion

open Ix.Compiler.Ixon (Address Constant)

namespace Lowered

variable {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
  {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}

/-- The same actual selected execution satisfies semantic preservation and
terminal resource guarantees, with no caller-supplied heap invariant. -/
theorem physicalMainResources (lowered : Lowered recovery fuel)
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    (sourceRun : IxIR0.eval lowered.compilation.sourceCtx sourceFuel []
      lowered.compilation.main = .ok sourceValue) :
    ∃ controlFuel heapFuel result,
      IxIR2.Eval.runMain
        (IxIR2.Eval.Context.ofProgram lowered.reuse.target
          lowered.attached.target.artifact.validationContext.schemas)
        .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
      lowered.PhysicalValueRel sourceValue result ∧ result.SharedResources := by
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
  obtain ⟨controlFuel, heapFuel, result, baseline, locRel, run, baselineRelation,
      heaps, values, resources⟩ :=
    lowered.attached.selectedPhysicalMainResources lowered.reuse attachedRun
  exact ⟨controlFuel, heapFuel, result, run,
    ⟨store, value, baseline, locRel, ⟨rawStore, addressImage, graph⟩,
      baselineRelation, heaps, values⟩, resources⟩

end Lowered

namespace Compilation

variable {constants : List (Address × Constant)} {root : Address}
  {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}

/-- Each branch retains the D2 semantic relation and adds a successful release
of that very returned value. Recovered shared results additionally carry the
physical allocation accounting theorem, before and after release. -/
def SelectedExecutionWithResources
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) : Prop :=
  match compilation.outcome with
  | .literal _ =>
      ∃ targetFuel store value,
        IxIR1.runOwnedMain (compilation.source.lowering.result.addressedCtx (fun _ _ => none))
          .shared compilation.source.artifact.main targetFuel = .ok (store, value) ∧
        compilation.LiteralValueRel sourceValue store value ∧
        ∃ releaseFuel released,
          IxIR1.dropVal (compilation.source.lowering.result.addressedCtx (fun _ _ => none))
            releaseFuel store value = .ok released ∧ released.live = 0
  | .recovered _ lowered =>
      ∃ rawValue controlFuel heapFuel result,
        compilation.SourceValueRel sourceValue rawValue ∧
        IxIR2.Eval.runMain
          (IxIR2.Eval.Context.ofProgram lowered.reuse.target
            lowered.attached.target.artifact.validationContext.schemas)
          .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
        lowered.PhysicalValueRel rawValue result ∧ result.SharedResources

/-- Forgetting resource evidence recovers the unchanged D2 semantic endpoint. -/
theorem SelectedExecutionWithResources.semantic
    {compilation : Compilation constants root config eraseFuel lowerFuel}
    {sourceValue : Ixon.Eval.Value}
    (execution : compilation.SelectedExecutionWithResources sourceValue) :
    compilation.SelectedExecution sourceValue := by
  cases selected : compilation.outcome with
  | literal reason =>
      simp only [SelectedExecutionWithResources, SelectedExecution, selected] at execution ⊢
      obtain ⟨fuel, store, value, run, relation, release⟩ := execution
      exact ⟨fuel, store, value, run, relation⟩
  | recovered recovery lowered =>
      simp only [SelectedExecutionWithResources, SelectedExecution, selected] at execution ⊢
      obtain ⟨raw, control, heap, result, source, run, relation, resources⟩ := execution
      exact ⟨raw, control, heap, result, source, run, relation⟩

/-- Successful Ixon evaluation supplies the actual selected execution, its
existing physical value relation, and complete shared-result reclamation.
The only caller premises are the original source sharing/oracle contracts. -/
theorem sourceRefinesSelectedWithResources
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    compilation.SelectedExecutionWithResources sourceValue := by
  cases selected : compilation.outcome with
  | literal reason =>
      obtain ⟨targetFuel, store, value, run, relation⟩ :=
        compilation.literalSourceRefines horacles hctx hsource
      have bodyRun : IxIR1.runMain
          (compilation.source.lowering.result.addressedCtx (fun _ _ => none))
          compilation.source.artifact.main targetFuel = .ok (store, value) :=
        (IxIR1.Sim.runOwnedMain_ok run).1
      obtain ⟨releaseFuel, released, release, empty⟩ :=
        compilation.source.lowered.reclamation (fun _ _ => none) bodyRun
      simp only [SelectedExecutionWithResources, selected]
      exact ⟨targetFuel, store, value, run, relation, releaseFuel, released, release, empty⟩
  | recovered recovery lowered =>
      obtain ⟨rawFuel, rawValue, rawRun, sourceRelation⟩ :=
        compilation.sourceRefines horacles hctx hsource
      rw [selected] at rawRun
      obtain ⟨controlFuel, heapFuel, result, run, relation, resources⟩ :=
        lowered.physicalMainResources rawRun
      simp only [SelectedExecutionWithResources, selected]
      exact ⟨rawValue, controlFuel, heapFuel, result, sourceRelation, run, relation, resources⟩

end Compilation

end Ix.Compiler.Recursion
