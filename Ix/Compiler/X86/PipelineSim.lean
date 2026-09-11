import Ix.Compiler.IxIR2.PipelinePhysical
import Ix.Compiler.X86.Select

/-! Source evaluation through the validated baseline and the actual scalar
selector result, ending at the typed local System V machine. -/

namespace Ix.Compiler.X86.Select

open Ix.Compiler
open Ix.Compiler.Pipeline
open Ix.Compiler.IxIR1.Lower
open Ix.Compiler.IxIR1.LowerSim

/-- The composed scalar boundary keeps the source sharing and oracle
obligations of `ValidatedCompilation.semanticForwardSimulation`. Erasure,
addressed execution, owned execution, interpretation transport, and selection
facts are derived from the exact returned artifacts. -/
theorem sourceRefines
    {constants : List (Ixon.Address × Ixon.Constant)}
    {mainAddress : Ixon.Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (attached : IxIR2.Pipeline.Attached constants mainAddress config .shared eraseFuel lowerFuel)
    (selected : Output attached.target.artifact.program)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (hctx : (validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (validatedEvalCtx constants config) sourceFuel
      (validatedMainFrame mainAddress) [] validatedMainSource = .ok sourceValue)
    (core : X86.Core) :
    ∃ rawValue ir1Fuel ir1Store controlFuel heapFuel physicalResult,
      @Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
        sourceValue rawValue attached.source.memberScope ∧
      MutualAddressedValueGraph
        (IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap)
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw)
        attached.source.functionRel ir1Store rawValue (.lit (.nat selected.word.toNat)) ∧
      IxIR1.runOwnedMain attached.compiled.simulationSourceContext .shared
        attached.target.artifact.source.main ir1Fuel =
          .ok (ir1Store, .lit (.nat selected.word.toNat)) ∧
      IxIR2.Eval.runMain attached.compiled.simulationTargetContext .physical
        attached.target.artifact.program controlFuel heapFuel = .ok physicalResult ∧
      IxIR2.Lower.Sim.OutcomeRel (ir1Store, .lit (.nat selected.word.toNat)) physicalResult ∧
      (X86.runFrom X86.Runtime.rejecting selected.target 2 core).status = .halted selected.word ∧
      (X86.runFrom X86.Runtime.rejecting selected.target 2 core).core.readReg .rsp = core.readReg .rsp := by
  letI : Sim.MemberScope := attached.source.memberScope
  have hframe : (validatedMainFrame mainAddress).SharingWF := by
    constructor
    · rfl
    · intro index member found
      simp [validatedMainFrame] at found
  have hbelow : Ixon.Sharing.sharesBelow
      (validatedMainFrame mainAddress).sharing.size validatedMainSource = true := rfl
  have herase : EraseAddressed.run
      (EraseValidator.eraseCtxOf (validatedEvalCtx constants config))
      constants attached.source.entry.target eraseFuel = .ok attached.source.erasure.result := by
    rw [attached.source.entryTarget]
    exact attached.source.erasure.runEq
  obtain ⟨traceFuel, addressedValue, trace, sourceRelation⟩ :=
    CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members
      (fun _ _ => none)
      (IxIR0.Readdress.Oracle.readdress attached.source.erasure.result.addressMap (fun _ _ => none))
      attached.source.members attached.source.entry herase
      (IxIR0.Readdress.Oracle.readdress_compatible
        (IxIR0.Readdress.Oracle.Readdressable.empty attached.source.erasure.result.addressMap))
      horacles hctx hframe hbelow hsource
  obtain ⟨rawValue, sourceRelation, addressedValueEq⟩ := sourceRelation
  subst addressedValue
  have lowered : (lowerAllAction attached.source.erasure.result.declarations
      attached.source.erasure.result.main .shared lowerFuel).run {} =
      .ok (attached.source.lowering.raw, attached.source.lowering.mainCode)
        attached.source.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using attached.source.lowering.lowerRun
  have progress := lowerAllAction_main_progress_of_trace_sealed rfl lowered
    (fun member => attached.source.exactTargetCtx_decls_of_mem (fun _ _ => none) member)
    (attached.source.exactExtraRepresented (fun _ _ => none))
    (attached.source.exactCompilerContracts (fun _ _ => none)).1
    (attached.source.externValueContract (fun _ _ => none))
    (attached.source.externTraceProgressContract (fun _ _ => none)) trace
  have simulation : SemanticForwardSimulation attached.source.addressedSourceCtx
      (attached.source.exactTargetCtx (fun _ _ => none))
      attached.source.erasure.result.main attached.source.lowering.mainCode
      attached.source.functionRel := by
    apply lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed rfl lowered
      (fun member => attached.source.exactTargetCtx_decls_of_mem (fun _ _ => none) member)
      (attached.source.exactExtraRepresented (fun _ _ => none))
      (attached.source.exactCompilerContracts (fun _ _ => none)).1
      (attached.source.externValueContract (fun _ _ => none))
    intro _ _ _
    exact progress
  obtain ⟨ir1Fuel, rawStore, ir1Value, rawRun, graph⟩ := simulation trace.run
  let rename := attached.source.lowering.result.rebuildRename attached.source.lowering.raw
  let ir1Store := IxIR1.Readdress.Store.mapAddresses rename rawStore
  have ownership := lowerAllAction_main_owned lowered
    (attached.source.exactExtraRepresented (fun _ _ => none))
    (attached.source.exactCompilerContracts (fun _ _ => none)).1 rawRun
  have rawWorld : IxIR1.Sim.HasWorld rawStore .shared ir1Value :=
    ownership.roots_world ⟨.shared, ir1Value⟩ (by simp)
  have finalWorld : IxIR1.Sim.HasWorld ir1Store .shared ir1Value :=
    (IxIR1.Sim.hasWorld_mapAddresses_iff rename rawStore .shared ir1Value).mpr rawWorld
  have sourceRun : IxIR1.runMain attached.compiled.simulationSourceContext
      attached.source.lowering.result.main ir1Fuel = .ok (ir1Store, ir1Value) := by
    have audit : attached.source.lowering.result.rebuildSemanticAudit
        attached.source.lowering.raw attached.source.lowering.mainCode = true :=
      attached.compiled.sourceRebuildSemanticAudit
    have renames : IxIR1.Readdress.Ctx.Renames rename
        (attached.source.exactTargetCtx (fun _ _ => none))
        attached.compiled.simulationSourceContext := attached.compiled.sourceContextRenames
    rw [attached.source.lowering.result.main_eq_rebuildMapAddresses audit]
    rw [IxIR1.Readdress.runMain_mapAddresses renames
      attached.source.lowering.mainCode ir1Fuel, rawRun]
    rfl
  have mainEq : attached.target.artifact.source.main = attached.source.lowering.result.main := by
    rw [attached.targetSourceProduced, attached.inputProduced]
    rfl
  have resultEq : attached.target.artifact.source.mainResult = .shared := by
    rw [attached.targetSourceProduced, attached.inputProduced]
  have ownedRun : IxIR1.runOwnedMain attached.compiled.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main ir1Fuel =
      .ok (ir1Store, ir1Value) := by
    rw [mainEq, resultEq]
    unfold IxIR1.runOwnedMain
    change (IxIR1.runMain attached.compiled.simulationSourceContext
      attached.source.lowering.result.main ir1Fuel >>= IxIR1.checkResultWorld .shared) = _
    rw [sourceRun]
    simp [IxIR1.checkResultWorld, IxIR1.Sim.rval_hasWorld_eq_true_iff.mpr finalWorld]
  obtain ⟨controlFuel, heapFuel, physicalResult, physicalRun, related⟩ :=
    attached.compiled.successfulPhysicalMainSimulation ownedRun
  obtain ⟨value, targetRun, stackPreserved⟩ := selected.refinesSuccessfulRun physicalRun core
  have ir1ValueEq : ir1Value = .lit (.nat selected.word.toNat) := related.value.symm.trans value
  subst ir1Value
  refine ⟨rawValue, ir1Fuel, ir1Store, controlFuel, heapFuel, physicalResult,
    sourceRelation, ⟨rawStore, rfl, graph⟩, ?_, physicalRun, related, targetRun, stackPreserved⟩
  simpa only [resultEq] using ownedRun

/-- A source Nat is returned exactly as a native word, without truncation.
This specialization makes the scalar observation explicit at both ends. -/
theorem sourceScalarRefines
    {constants : List (Ixon.Address × Ixon.Constant)}
    {mainAddress : Ixon.Address} {config : Pipeline.Config}
    {eraseFuel lowerFuel : Nat}
    (attached : IxIR2.Pipeline.Attached constants mainAddress config .shared eraseFuel lowerFuel)
    (selected : Output attached.target.artifact.program)
    {sourceFuel number : Nat}
    (horacles : @Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (hctx : (validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (validatedEvalCtx constants config) sourceFuel
      (validatedMainFrame mainAddress) [] validatedMainSource = .ok (.litV (.natL number)))
    (core : X86.Core) :
    selected.word.toNat = number ∧
      (X86.runFrom X86.Runtime.rejecting selected.target 2 core).status = .halted selected.word ∧
      (X86.runFrom X86.Runtime.rejecting selected.target 2 core).core.readReg .rsp = core.readReg .rsp := by
  obtain ⟨rawValue, _, _, _, _, _, sourceRelation, graph, _, _, _, targetRun, stackPreserved⟩ :=
    sourceRefines attached selected horacles hctx hsource core
  have literal : rawValue = .lit (.nat number) := by
    simp only [Sim.InlinedValRel, Ixon.Eval.Value.inlineSharing] at sourceRelation
    cases sourceRelation
    rfl
  subst rawValue
  obtain ⟨_, _, graph⟩ := graph
  have numberEq : number = selected.word.toNat := by
    simp only [IxIR0.Readdress.Value.mapAddresses] at graph
    cases graph
    rfl
  exact ⟨numberEq.symm, targetRun, stackPreserved⟩

end Ix.Compiler.X86.Select
