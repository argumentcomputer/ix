import Ix.Compiler.Recursion.Sim
import Ix.Compiler.Recursion.Trace
import Ix.Compiler.LoweredCompilationSim
import Ix.Compiler.IxIR2.PipelinePhysical
import Ix.Compiler.IxIR2.ReuseLiveSim

/-!
# Selected source execution through physical reuse

The exact checked recovery supplies projection-free trace completeness.
Ownership lowering, complete addressing, baseline physical execution, and
the selected reuse result then compose through the common attachment.
Literal fallback retains the original validated owned IxIR₁ endpoint.
-/

namespace Ix.Compiler.Recursion

open Ix.Compiler.Ixon (Address Constant)

namespace Lowered

variable {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
  {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}

/-- The existing value/heap relations composed across full addressing,
baseline lowering, and physical reuse. Allocation counters are not part of
this semantic relation. -/
def PhysicalValueRel (lowered : Lowered recovery fuel) (sourceValue : IxIR0.Value)
    (result : IxIR2.Eval.Result) : Prop :=
  ∃ store value baseline locRel,
    IxIR1.LowerSim.AddressedValueGraph
      (lowered.lowering.result.rebuildRename lowered.lowering.raw)
      lowered.compilation.functionRel store sourceValue value ∧
    IxIR2.Lower.Sim.OutcomeRel (store, value) baseline ∧
    IxIR2.ReuseSim.StableHeapRel baseline.store result.store locRel ∧
    IxIR1.Sim.RValIso locRel baseline.value result.value

/-- No intermediate run or compiler invariant is supplied by the caller.
The selected program may be the validated rewrite or its checked baseline. -/
theorem physicalMainSimulation (lowered : Lowered recovery fuel)
    {sourceFuel : Nat} {sourceValue : IxIR0.Value}
    (sourceRun : IxIR0.eval lowered.compilation.sourceCtx sourceFuel []
      lowered.compilation.main = .ok sourceValue) :
    ∃ controlFuel heapFuel result,
      IxIR2.Eval.runMain
        (IxIR2.Eval.Context.ofProgram lowered.reuse.target
          lowered.attached.target.artifact.validationContext.schemas)
        .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
      lowered.PhysicalValueRel sourceValue result := by
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
  obtain ⟨controlFuel, heapFuel, baseline, baselineRun, baselineRelation⟩ :=
    lowered.attached.successfulPhysicalMainSimulation attachedRun
  obtain ⟨selectedControl, result, locRel, selectedRun, heapRelation, valueRelation, _budget⟩ :=
    IxIR2.ReuseLiveSim.selectedPhysicalMainSimulation (attached := lowered.attached)
      (oracle := fun _ _ => none) lowered.reuse baselineRun
  exact ⟨selectedControl, heapFuel, result, selectedRun, store, value, baseline, locRel,
    ⟨rawStore, addressImage, graph⟩, baselineRelation, heapRelation, valueRelation⟩

end Lowered

namespace Compilation

variable {constants : List (Address × Constant)} {root : Address}
  {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}

abbrev SourceValueRel (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) (rawValue : IxIR0.Value) : Prop :=
  @Ix.Compiler.Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList compilation.source.erasure.result.raw }
    sourceValue rawValue compilation.source.memberScope

def LiteralValueRel (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) (store : IxIR1.Store) (value : IxIR1.RVal) : Prop :=
  ∃ rawValue,
    compilation.SourceValueRel sourceValue rawValue ∧
    IxIR1.LowerSim.MutualAddressedValueGraph
      (IxIR0.MutualBlock.Renaming.apply compilation.source.erasure.result.addressMap)
      (compilation.source.lowering.result.rebuildRename compilation.source.lowering.raw)
      compilation.source.lowered.functionRel store rawValue value

/-- The executable outcome determines the theorem's target: the original
owned IxIR₁ on literal fallback, or the exact selected physical IxIR₂ after
successful recovery and attachment. -/
def SelectedExecution (compilation : Compilation constants root config eraseFuel lowerFuel)
    (sourceValue : Ixon.Eval.Value) : Prop :=
  match compilation.outcome with
  | .literal _ =>
      ∃ targetFuel store value,
        IxIR1.runOwnedMain (compilation.source.lowering.result.addressedCtx (fun _ _ => none))
          .shared compilation.source.artifact.main targetFuel = .ok (store, value) ∧
        compilation.LiteralValueRel sourceValue store value
  | .recovered _ lowered =>
      ∃ rawValue controlFuel heapFuel result,
        compilation.SourceValueRel sourceValue rawValue ∧
        IxIR2.Eval.runMain
          (IxIR2.Eval.Context.ofProgram lowered.reuse.target
            lowered.attached.target.artifact.validationContext.schemas)
          .physical lowered.reuse.target controlFuel heapFuel = .ok result ∧
        lowered.PhysicalValueRel rawValue result

/-- The original source certificate also supplies the literal fallback's
call-aware trace. It crosses the same generic ownership theorem as recovery. -/
theorem literalSourceRefines
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    ∃ targetFuel store value,
      IxIR1.runOwnedMain (compilation.source.lowering.result.addressedCtx (fun _ _ => none))
        .shared compilation.source.artifact.main targetFuel = .ok (store, value) ∧
      compilation.LiteralValueRel sourceValue store value := by
  letI : Ix.Compiler.Sim.MemberScope := compilation.source.memberScope
  have hframe : (Pipeline.validatedMainFrame root).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [Pipeline.validatedMainFrame] at found
  have hbelow : Ixon.Sharing.sharesBelow (Pipeline.validatedMainFrame root).sharing.size
      Pipeline.validatedMainSource = true := rfl
  have herase : EraseAddressed.run
      (EraseValidator.eraseCtxOf (Pipeline.validatedEvalCtx constants config)) constants
      compilation.source.entry.target eraseFuel = .ok compilation.source.erasure.result := by
    rw [compilation.source.entryTarget]
    exact compilation.source.erasure.runEq
  obtain ⟨traceFuel, addressedValue, trace, rawValue, sourceRelation, addressedEq⟩ :=
    IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members
      (fun _ _ => none) (fun _ _ => none) compilation.source.members compilation.source.entry herase
      (by intro address arguments; rfl) horacles hctx hframe hbelow hsource
  subst addressedValue
  obtain ⟨targetFuel, rawStore, store, value, ownedRun, addressImage, graph⟩ :=
    compilation.source.lowered.addressedOwnedMain trace
  exact ⟨targetFuel, store, value, ownedRun, rawValue, sourceRelation,
    rawStore, addressImage, graph⟩

/-- Source-facing semantic preservation for every successful compilation
outcome. The only caller premises are the existing source sharing/oracle
contracts and successful Ixon evaluation. -/
theorem sourceRefinesSelected
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    compilation.SelectedExecution sourceValue := by
  cases selected : compilation.outcome with
  | literal reason =>
      simpa only [SelectedExecution, selected] using
        compilation.literalSourceRefines horacles hctx hsource
  | recovered recovery lowered =>
      obtain ⟨rawFuel, rawValue, rawRun, sourceRelation⟩ :=
        compilation.sourceRefines horacles hctx hsource
      rw [selected] at rawRun
      obtain ⟨controlFuel, heapFuel, result, run, related⟩ :=
        lowered.physicalMainSimulation rawRun
      simp only [SelectedExecution, selected]
      exact ⟨rawValue, controlFuel, heapFuel, result, sourceRelation, run, related⟩

end Compilation

end Ix.Compiler.Recursion
