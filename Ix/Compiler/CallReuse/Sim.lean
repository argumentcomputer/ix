import Ix.Compiler.CallReuse.Pipeline
import Ix.Compiler.LoweredCompilationSim
import Ix.Compiler.IxIR2.PipelineCallReuse

/-!
# Source refinement with suspended call credits

The original shared-source certificate supplies a call-aware erasure trace.
The ordinary ownership compiler and exact checked attachment supply execution,
ownership, and the physical baseline. The versioned selection then supplies
the same semantic heap/value relations and R4 resource and cost laws.
-/

namespace Ix.Compiler.CallReuse.Compilation

open Ix.Compiler.Ixon (Address Constant)

variable {constants : List (Address × Constant)} {root : Address}
  {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}

abbrev SourceValueRel (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) (rawValue : IxIR0.Value) : Prop :=
  @Ix.Compiler.Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList compilation.attached.source.erasure.result.raw }
    sourceValue rawValue compilation.attached.source.memberScope

/-- The existing source, address, baseline, and live-heap relations composed
without any counter condition in their semantic meaning. -/
def PhysicalValueRel (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) (result : IxIR2.Eval.Result) : Prop :=
  ∃ rawValue store value baseline locRel,
    compilation.SourceValueRel sourceValue rawValue ∧
    IxIR1.LowerSim.MutualAddressedValueGraph
      (IxIR0.MutualBlock.Renaming.apply compilation.attached.source.erasure.result.addressMap)
      (compilation.attached.source.lowering.result.rebuildRename compilation.attached.source.lowering.raw)
      compilation.attached.source.lowered.functionRel store rawValue value ∧
    IxIR2.Lower.Sim.OutcomeRel (store, value) baseline ∧
    IxIR2.ReuseSim.StableHeapRel baseline.store result.store locRel ∧
    IxIR1.Sim.RValIso locRel baseline.value result.value

/-- Source correctness, full shared-result reclamation, allocation/free laws,
RC and peak bounds for every accepted shared compilation and either selection
branch. Only the original source sharing/oracle contracts and evaluation are
premises; ownership and all compiler/heap/cost facts are derived internally. -/
theorem sourceRefinesWithCostLaws
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.attached.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.attached.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    ∃ controlFuel heapFuel result,
      IxIR2.Eval.Policy.runMain compilation.selection.policy
        (IxIR2.Eval.Context.ofProgram compilation.selection.target
          compilation.attached.target.artifact.validationContext.schemas)
        .physical compilation.selection.target controlFuel heapFuel = .ok result ∧
      compilation.PhysicalValueRel sourceValue result ∧ result.SharedResources ∧
      compilation.attached.compiled.CallCostComparison compilation.selection heapFuel result := by
  let source := compilation.attached.source
  letI : Ix.Compiler.Sim.MemberScope := source.memberScope
  have hframe : (Pipeline.validatedMainFrame root).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [Pipeline.validatedMainFrame] at found
  have hbelow : Ixon.Sharing.sharesBelow (Pipeline.validatedMainFrame root).sharing.size
      Pipeline.validatedMainSource = true := rfl
  have herase : EraseAddressed.run
      (EraseValidator.eraseCtxOf (Pipeline.validatedEvalCtx constants config)) constants
      source.entry.target eraseFuel = .ok source.erasure.result := by
    rw [source.entryTarget]
    exact source.erasure.runEq
  obtain ⟨traceFuel, addressedValue, trace, rawValue, sourceRelation, addressedEq⟩ :=
    IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members
      (fun _ _ => none) (fun _ _ => none) source.members source.entry herase
      (by intro address arguments; rfl) horacles hctx hframe hbelow hsource
  subst addressedValue
  obtain ⟨ir1Fuel, rawStore, store, value, ownedRun, addressImage, graph⟩ :=
    source.lowered.addressedOwnedMain trace
  have attachedRun : IxIR1.runOwnedMain compilation.attached.compiled.simulationSourceContext
      compilation.attached.compiled.target.artifact.source.mainResult
      compilation.attached.compiled.target.artifact.source.main ir1Fuel = .ok (store, value) := by
    rw [compilation.attached.compiled.simulationSourceContext_eq_addressedCtx,
      compilation.attached.compiled.targetSourceProduced, compilation.attached.compiled.inputProduced]
    exact ownedRun
  obtain ⟨baselineControl, controlFuel, heapFuel, baseline, result, locRel,
      baselineRun, run, baselineRelation, heaps, values, baselineResources, resources,
      allocations, costs, reclaimed, prefixes⟩ :=
    compilation.attached.compiled.selectedCallPhysicalMainCostLaws compilation.selection attachedRun
  exact ⟨controlFuel, heapFuel, result, run,
    ⟨rawValue, store, value, baseline, locRel, sourceRelation,
      ⟨rawStore, addressImage, graph⟩, baselineRelation, heaps, values⟩,
    resources, baselineControl, heapFuel, baseline, baselineRun, baselineResources,
    allocations, costs, reclaimed, prefixes⟩

end Ix.Compiler.CallReuse.Compilation
