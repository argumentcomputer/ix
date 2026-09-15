import Compilatrix.IxIR1.Lower
import Compilatrix.IxIR1.LowerAddressedSim
import Compilatrix.IxIR1.LowerFullyAddressedSim
import Compilatrix.IxIR1.LowerMutualAddressedProgress
import Compilatrix.IxIR1.LowerMutualAddressedSim
import Compilatrix.IxIR1.LowerProgress
import Compilatrix.IxIR1.LowerSim
import Compilatrix.IxIR1.LowerStateSim

/-! Required axiom fences for Lowering; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.IxIR1.LowerSim.reclamation_of_run_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.reclamation_of_run_invariants

/-- info: 'Compilatrix.IxIR1.LowerSim.reclamation_of_run_ownership_and_zero_reuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.reclamation_of_run_ownership_and_zero_reuses

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_main_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_main_owned

/-- info: 'Compilatrix.IxIR1.LowerSim.RunCostInvariant.costRefinement' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.RunCostInvariant.costRefinement

/-- info: 'Compilatrix.IxIR1.LowerSim.CostRefinement.and' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CostRefinement.and

/-- info: 'Compilatrix.IxIR1.LowerSim.allocationFreeCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.allocationFreeCostRefinement

/-- info: 'Compilatrix.IxIR1.LowerSim.papp_graph_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.papp_graph_op

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_memoryErrorUnreachable_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_memoryErrorUnreachable_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_unknownRefUnreachable_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_unknownRefUnreachable_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.AddressedSemanticForwardSimulation.precomposeIxIR0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.AddressedSemanticForwardSimulation.precomposeIxIR0

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_after_addressedErasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_after_addressedErasure

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_protectsSourceAddresses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_protectsSourceAddresses

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_memoryErrorUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_memoryErrorUnreachable

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_ordinaryStuckUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_ordinaryStuckUnreachable

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_unknownRefUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_unknownRefUnreachable

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain_cost

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact_success

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_apply_constructorIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_apply_constructorIdentity

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_exact

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_memoryErrorUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_memoryErrorUnreachable

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_ordinaryStuckUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_ordinaryStuckUnreachable

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_unknownRefUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_unknownRefUnreachable

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_cost

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_after_addressedErasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_after_addressedErasure

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_exact_after_addressedErasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_exact_after_addressedErasure

/-- info: 'Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_erasure

/-- info: 'Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_with_members

/-- info: 'Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_inlineSharing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_inlineSharing

/-- info: 'Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_certifiedSharedClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.ProjectionSafeEval.of_certifiedSharedClosed

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_inlineSharing_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_inlineSharing_with_members

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_with_members

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_with_members

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_main_progress_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_main_progress_of_certificate_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation_of_certificate_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_certificate_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_addressed_certificate_with_members_exact_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_addressed_certificate_with_members_exact_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_exact_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_exact_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_compilerTraceProgressContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_compilerTraceProgressContracts

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_main_progress_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_main_progress_of_certificate_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_main_progress_of_projectionSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_main_progress_of_projectionSafe

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_ordinaryStuckUnreachable_of_erasure_inlineSharing_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_ordinaryStuckUnreachable_of_erasure_inlineSharing_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_erasure_inlineSharing_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_erasure_inlineSharing_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_trace_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_trace_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_sourceDeclLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_sourceDeclLayout

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_sourcePapSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_sourcePapSafe

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_fnDeclCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_fnDeclCovered

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_extraProvenance_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_extraProvenance_empty

/-- info: 'Compilatrix.IxIR1.LowerSim.GeneratedDeclProvenance.fnPreservesAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.GeneratedDeclProvenance.fnPreservesAt

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_sourceFnPreservesAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_sourceFnPreservesAt

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_compilerContracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_compilerContracts

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerDecl_defn_papSafe_of_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerDecl_defn_papSafe_of_run

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerDecl_recursor_papSafe_of_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerDecl_recursor_papSafe_of_run

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_compilerFunction_declPapSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_compilerFunction_declPapSafe

/-- info: 'Compilatrix.IxIR1.LowerSim.SourceAllShared.papSafe' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.SourceAllShared.papSafe

/-- info: 'Compilatrix.IxIR1.LowerSim.sourcePapSafe_not_sourceAllShared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.sourcePapSafe_not_sourceAllShared

/-- info: 'Compilatrix.IxIR1.LowerSim.papSafeDeclContractsBelow_of_source_extra' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.papSafeDeclContractsBelow_of_source_extra

/-- info: 'Compilatrix.IxIR1.LowerSim.compilerContracts_of_source_extra_below_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.compilerContracts_of_source_extra_below_step

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerE_proj_var_run_value_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerE_proj_var_run_value_sound

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerE_proj_erasure_run_value_progress_within' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerE_proj_erasure_run_value_progress_within

/-- info: 'Compilatrix.IxIR1.Lower.lowerAllIndexed_eq_lowerAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Lower.lowerAllIndexed_eq_lowerAll
