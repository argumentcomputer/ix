import Compilatrix.AddressEnv
import Compilatrix.EraseAddressed
import Compilatrix.EraseAddressedSim
import Compilatrix.IxIR.Bounded
import Compilatrix.LoweredCompilationSim
import Compilatrix.Pipeline
import Compilatrix.PipelineApply
import Compilatrix.PipelineErasure
import Compilatrix.PipelineSound
import Compilatrix.Sim
import Compilatrix.SimApply
import Compilatrix.SimInstance
import Compilatrix.UsageSound

/-! Required axiom fences for Erasure; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Sim.erasure_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim

/-- info: 'Compilatrix.Sim.erasure_sim_with_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_with_members

/-- info: 'Compilatrix.Sim.erasure_sim_projectionSafe_with_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_projectionSafe_with_members

/-- info: 'Compilatrix.Sim.erasure_sim_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_closed

/-- info: 'Compilatrix.Sim.erasure_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_inlineSharing

/-- info: 'Compilatrix.Sim.erasure_sim_inlineSharing_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_inlineSharing_closed

/-- info: 'Compilatrix.Sim.erasure_proj_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_proj_sim

/-- info: 'Compilatrix.Sim.erasure_proj_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_proj_sim_inlineSharing

/-- info: 'Compilatrix.SimInstance.ghostDefinitionHeadSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.ghostDefinitionHeadSim

/-- info: 'Compilatrix.SimInstance.quotientIndSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.quotientIndSim

/-- info: 'Compilatrix.SimInstance.externAnswerSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.externAnswerSim

/-- info: 'Compilatrix.SimInstance.pairSplitProjectionSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.pairSplitProjectionSim

/-- info: 'Compilatrix.SimInstance.indexedRecSplitSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.indexedRecSplitSim

/-- info: 'Compilatrix.SimInstance.indexedRecSelfSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.indexedRecSelfSim

/-- info: 'Compilatrix.SimInstance.definitionProjectionSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.definitionProjectionSim

/-- info: 'Compilatrix.SimInstance.mutualInductiveMemberSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.mutualInductiveMemberSim

/-- info: 'Compilatrix.SimInstance.cyclicDefinitionMembersSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.cyclicDefinitionMembersSim

/-- info: 'Compilatrix.SimInstance.cyclicRecursorMembersSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.cyclicRecursorMembersSim

/-- info: 'Compilatrix.SimInstance.opaqueMutualMemberSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.opaqueMutualMemberSim

/-- info: 'Compilatrix.SimInstance.opaqueMutualProjectionSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.opaqueMutualProjectionSim

/-- info: 'Compilatrix.UsageSound.computedErased_eval_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UsageSound.computedErased_eval_noninterference

/-- info: 'Compilatrix.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceNoninterference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceNoninterference

/-- info: 'Compilatrix.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceSim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceSim

/-- info: 'Compilatrix.SimInstance.addIxIR1CompilerContracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1CompilerContracts

/-- info: 'Compilatrix.SimInstance.addIxIR1SemanticForwardSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1SemanticForwardSimulation

/-- info: 'Compilatrix.SimInstance.addIxIR1MemoryErrorUnreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1MemoryErrorUnreachable

/-- info: 'Compilatrix.SimInstance.addIxIR1DynamicCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1DynamicCostRefinement

/-- info: 'Compilatrix.EraseAddressed.run_readdressOracle_semantics_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.EraseAddressed.run_readdressOracle_semantics_of_run_eq_ok

/-- info: 'Compilatrix.Pipeline.Artifact.functionSummary_sound_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.functionSummary_sound_of_checkHPTWith_eq_ok

/-- info: 'Compilatrix.Pipeline.Artifact.functionSummary_sound_of_checkHPT_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.functionSummary_sound_of_checkHPT_eq_ok

/-- info: 'Compilatrix.Pipeline.Artifact.functionSummary_sound_of_producedHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.functionSummary_sound_of_producedHPT

/-- info: 'Compilatrix.Pipeline.Artifact.functionSummary_sound_of_cachedHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.functionSummary_sound_of_cachedHPT

/-- info: 'Compilatrix.Pipeline.Artifact.runCode_pruneCase_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runCode_pruneCase_of_checkHPTWith_eq_ok

/-- info: 'Compilatrix.Pipeline.Artifact.runCode_pruneCaseWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runCode_pruneCaseWithProducedHPT_eq

/-- info: 'Compilatrix.Pipeline.Artifact.runCode_pruneCaseWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runCode_pruneCaseWithCachedHPT_eq

/-- info: 'Compilatrix.Pipeline.Artifact.runCode_pruneCasesRecursive_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runCode_pruneCasesRecursive_of_checkHPTWith_eq_ok

/-- info: 'Compilatrix.Pipeline.Artifact.runCode_pruneCasesRecursiveWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runCode_pruneCasesRecursiveWithProducedHPT_eq

/-- info: 'Compilatrix.Pipeline.Artifact.runCode_pruneCasesRecursiveWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runCode_pruneCasesRecursiveWithCachedHPT_eq

/-- info: 'Compilatrix.Pipeline.Artifact.runMain_pruneMain_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runMain_pruneMain_of_checkHPTWith_eq_ok

/-- info: 'Compilatrix.Pipeline.Artifact.runMain_pruneMainWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runMain_pruneMainWithProducedHPT_eq

/-- info: 'Compilatrix.Pipeline.Artifact.runMain_pruneMainWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runMain_pruneMainWithCachedHPT_eq

/-- info: 'Compilatrix.Pipeline.Artifact.runMain_pruneProgram_of_checkAndPruneProgramWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runMain_pruneProgram_of_checkAndPruneProgramWith_eq_ok

/-- info: 'Compilatrix.EraseAddressed.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.EraseAddressed.semanticAudit_of_run_eq_ok

/-- info: 'Compilatrix.EraseAddressed.run_semantics_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.EraseAddressed.run_semantics_of_run_eq_ok

/-- info: 'Compilatrix.EraseAddressed.run_projectionSafeMain_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.EraseAddressed.run_projectionSafeMain_of_run_eq_ok

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.targetDeclEnv_ne_extern' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.targetDeclEnv_ne_extern

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.externValueContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.externValueContract

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.externTraceProgressContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.externTraceProgressContract

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.semanticForwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.semanticForwardSimulation

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.semanticForwardSimulationOfProducedOptimizedArtifact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.semanticForwardSimulationOfProducedOptimizedArtifact

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.targetProgressAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.targetProgressAfterProducedOptimization

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.memoryErrorUnreachableAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.memoryErrorUnreachableAfterProducedOptimization

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.reclamationAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.reclamationAfterProducedOptimization

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.allocationFreeCostInvariantAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.allocationFreeCostInvariantAfterProducedOptimization

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.sourceCallableRowsSelected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.sourceCallableRowsSelected

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.sourceDeclLayout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.sourceDeclLayout

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.sourcePapSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.sourcePapSafe

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.fnDeclCovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.fnDeclCovered

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.exactExtraRepresented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.exactExtraRepresented

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.exactCompilerContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.exactCompilerContracts

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.targetProgress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.targetProgress

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.memoryErrorUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.memoryErrorUnreachable

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.reclamation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.reclamation

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.costRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.costRefinement

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.ownershipAmortizedCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.ownershipAmortizedCostRefinement

/-- info: 'Compilatrix.AddressEnv.lookup_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.AddressEnv.lookup_build

/-- info: 'Compilatrix.Pipeline.ResolverIndex.resolve_ofList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ResolverIndex.resolve_ofList

/-- info: 'Compilatrix.Pipeline.LoweredCompilation.exactCompilerContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.LoweredCompilation.exactCompilerContracts

/-- info: 'Compilatrix.Pipeline.LoweredCompilation.addressedOwnedMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.LoweredCompilation.addressedOwnedMain

/-- info: 'Compilatrix.Pipeline.LoweredCompilation.reclamation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.LoweredCompilation.reclamation

/-- info: 'Compilatrix.Pipeline.LoweredCompilation.owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.LoweredCompilation.owned

/-- info: 'Compilatrix.Pipeline.CertifiedErasure.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.CertifiedErasure.sourceRefines

/-- info: 'Compilatrix.Sim.apply_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.apply_sim_inlineSharing

/-- info: 'Compilatrix.Sim.apply_sim_projectionSafe_with_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.apply_sim_projectionSafe_with_members

/-- info: 'Compilatrix.Sim.applyMany_sim_projectionSafe_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.applyMany_sim_projectionSafe_inlineSharing

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.runtimeApply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.runtimeApply

/-- info: 'Compilatrix.Pipeline.ValidatedCompilation.runtimeTraceRenames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedCompilation.runtimeTraceRenames

/-- info: 'Compilatrix.IxIR.Bounded.getNatFuel_spec_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR.Bounded.getNatFuel_spec_le

/-- info: 'Compilatrix.IxIR.Bounded.getListAcc_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR.Bounded.getListAcc_spec

/-- info: 'Compilatrix.IxIR.Bounded.run_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR.Bounded.run_roundtrip

/-- info: 'Compilatrix.IxIR.Bounded.run_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR.Bounded.run_spec
