import Compilatrix.IxIR1.CostInstance
import Compilatrix.IxIR1.CostModel
import Compilatrix.IxIR1.CostTrace
import Compilatrix.IxIR1.Decode
import Compilatrix.IxIR1.Eval
import Compilatrix.IxIR1.EvalHistory
import Compilatrix.IxIR1.EvalIso
import Compilatrix.IxIR1.EvalRewrite
import Compilatrix.IxIR1.MutualBlock
import Compilatrix.IxIR1.NoReuse
import Compilatrix.IxIR1.NoReuseAddressed
import Compilatrix.IxIR1.OptimizerReclamation
import Compilatrix.IxIR1.RcPotential
import Compilatrix.IxIR1.Reachability
import Compilatrix.IxIR1.ReaddressAll
import Compilatrix.IxIR1.ReaddressAllSim
import Compilatrix.IxIR1.ReaddressIndex
import Compilatrix.IxIR1.ReaddressOwnership
import Compilatrix.IxIR1.ReaddressSim
import Compilatrix.IxIR1.Reclamation
import Compilatrix.IxIR1.Sim

/-! Required axiom fences for IxIR1; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.IxIR1.Sim.reuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.reuse_sound

/-- info: 'Compilatrix.IxIR1.Sim.reuse_shared_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.reuse_shared_sound

/-- info: 'Compilatrix.IxIR1.Sim.invoke_fn_result_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.invoke_fn_result_hasWorld

/-- info: 'Compilatrix.IxIR1.Reclamation.live_eq_zero_of_empty_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.live_eq_zero_of_empty_roots

/-- info: 'Compilatrix.IxIR1.Reclamation.shared_reclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.shared_reclamation

/-- info: 'Compilatrix.IxIR1.Reclamation.runMain_order_of_reuses_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runMain_order_of_reuses_eq_zero

/-- info: 'Compilatrix.IxIR1.Reclamation.runOp_order_of_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runOp_order_of_reuses_eq

/-- info: 'Compilatrix.IxIR1.NoReuse.runMain_reuses_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.runMain_reuses_eq_zero

/-- info: 'Compilatrix.IxIR1.NoReuse.runOp_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.runOp_reuses_eq

/-- info: 'Compilatrix.IxIR1.NoReuse.invoke_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.invoke_reuses_eq

/-- info: 'Compilatrix.IxIR1.NoReuse.applyGo_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.applyGo_reuses_eq

/-- info: 'Compilatrix.IxIR1.Sim.runOwnedMain_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runOwnedMain_ok

/-- info: 'Compilatrix.IxIR1.NoReuse.checkCode_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.checkCode_eq_true_iff

/-- info: 'Compilatrix.IxIR1.NoReuse.checkDeclarations_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.checkDeclarations_eq_true_iff

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllAction_noReuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllAction_noReuse

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllAction_reclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllAction_reclamation

/-- info: 'Compilatrix.IxIR1.NoReuse.reclamation_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.reclamation_mapAddresses

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_raw

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw

/-- info: 'Compilatrix.IxIR1.Reclamation.runMain_nodes_size_eq_allocs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runMain_nodes_size_eq_allocs

/-- info: 'Compilatrix.IxIR1.Reclamation.runMain_live_add_frees_eq_allocs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runMain_live_add_frees_eq_allocs

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllAction_reuseCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllAction_reuseCostRefinement

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllAction_costRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllAction_costRefinement

/-- info: 'Compilatrix.IxIR1.NoReuse.runCostInvariant_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.runCostInvariant_mapAddresses

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_runCostInvariant_of_exact_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_runCostInvariant_of_exact_raw

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reuseCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reuseCostRefinement

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_costRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_costRefinement

/-- info: 'Compilatrix.IxIR1.CostInstance.exactCostRefinement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostInstance.exactCostRefinement

/-- info: 'Compilatrix.IxIR1.CostInstance.loweringCostWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostInstance.loweringCostWitness

/-- info: 'Compilatrix.IxIR1.CostModel.lowerAllAction_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostModel.lowerAllAction_run

/-- info: 'Compilatrix.IxIR1.CostModel.sourceSensitiveCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostModel.sourceSensitiveCostRefinement

/-- info: 'Compilatrix.IxIR1.CostModel.sourceSensitiveBoundsCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostModel.sourceSensitiveBoundsCostRefinement

/-- info: 'Compilatrix.IxIR1.CostModel.loweringCostWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostModel.loweringCostWitness

/-- info: 'Compilatrix.IxIR1.CostTrace.ProfileCostRefinement.of_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.ProfileCostRefinement.of_witness

/-- info: 'Compilatrix.IxIR1.CostTrace.ObservationGrowthLE.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.ObservationGrowthLE.trans

/-- info: 'Compilatrix.IxIR1.CostTrace.dupVals_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.dupVals_growth

/-- info: 'Compilatrix.IxIR1.CostTrace.withinBudget_ownershipAmortized_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.withinBudget_ownershipAmortized_iff

/-- info: 'Compilatrix.IxIR1.CostTrace.RcPotentialGrowthLE.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.RcPotentialGrowthLE.trans

/-- info: 'Compilatrix.IxIR1.CostTrace.dupVals_rcPotential_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.dupVals_rcPotential_growth

/-- info: 'Compilatrix.IxIR1.CostTrace.dropVal_amortizedRc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.dropVal_amortizedRc

/-- info: 'Compilatrix.IxIR1.CostTrace.dropUVal_amortizedRc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.dropUVal_amortizedRc

/-- info: 'Compilatrix.IxIR1.CostTrace.runOp_localRcPotential_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.runOp_localRcPotential_growth

/-- info: 'Compilatrix.IxIR1.CostTrace.OpRcPotentialSound.of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.OpRcPotentialSound.of_local

/-- info: 'Compilatrix.IxIR1.CostTrace.EmitRcPotentialSound.comp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.EmitRcPotentialSound.comp

/-- info: 'Compilatrix.IxIR1.CostTrace.EmitRcPotentialSound.localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.EmitRcPotentialSound.localOp

/-- info: 'Compilatrix.IxIR1.CostTrace.dropVal_allocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.dropVal_allocs

/-- info: 'Compilatrix.IxIR1.CostTrace.runOp_localOwnership_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.runOp_localOwnership_growth

/-- info: 'Compilatrix.IxIR1.CostTrace.OpOwnershipCostSound.of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.OpOwnershipCostSound.of_local

/-- info: 'Compilatrix.IxIR1.CostTrace.EmitOwnershipCostSound.comp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.EmitOwnershipCostSound.comp

/-- info: 'Compilatrix.IxIR1.CostTrace.EmitOwnershipCostSound.localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.EmitOwnershipCostSound.localOp

/-- info: 'Compilatrix.IxIR1.CostTrace.ProfileFundedEmitStateRunSound.ofOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.ProfileFundedEmitStateRunSound.ofOp

/-- info: 'Compilatrix.IxIR1.CostTrace.ProfileFundedApplyRun.papOver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.ProfileFundedApplyRun.papOver

/-- info: 'Compilatrix.IxIR1.CostTrace.LowerResultProfileSound.installThen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.LowerResultProfileSound.installThen

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerE_let_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerE_let_run_profile_sound

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerBorrow_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerBorrow_run_profile_sound

/-- info: 'Compilatrix.IxIR1.CostTrace.projectionSlotReleased_profileFundedEmitStateRunSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.projectionSlotReleased_profileFundedEmitStateRunSound

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerE_proj_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerE_proj_run_profile_sound

/-- info: 'Compilatrix.IxIR1.CostTrace.LowerResultProfileSound.consArgs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.LowerResultProfileSound.consArgs

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerCaptures_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerCaptures_run_profile_sound

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerLam_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerLam_run_profile_sound

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerE_lam_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerE_lam_run_profile_sound

/-- info: 'Compilatrix.IxIR1.CostTrace.sourceProfileOwnershipAllowance_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.sourceProfileOwnershipAllowance_add

/-- info: 'Compilatrix.IxIR1.CostTrace.CodeOwnershipCostSound.runCertificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.CodeOwnershipCostSound.runCertificate

/-- info: 'Compilatrix.IxIR1.CostTrace.CodeOwnershipCostSound.withinBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.CodeOwnershipCostSound.withinBudget

/-- info: 'Compilatrix.IxIR1.CostTrace.OwnershipAmortizedRunCertificate.spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.OwnershipAmortizedRunCertificate.spec

/-- info: 'Compilatrix.IxIR1.CostTrace.ProfileCostRefinement.of_ownershipAmortizedCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.ProfileCostRefinement.of_ownershipAmortizedCertificate

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerAllAction_compilerProfileContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerAllAction_compilerProfileContracts

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerAllAction_main_ownershipAmortizedCertificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerAllAction_main_ownershipAmortizedCertificate_sealed

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerAllAction_profileCostRefinement_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerAllAction_profileCostRefinement_sealed

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_sealed

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_exact_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_exact_sealed

/-- info: 'Compilatrix.IxIR1.Readdress.evalTransportAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.evalTransportAt

/-- info: 'Compilatrix.IxIR1.Readdress.applyGo_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.applyGo_mapAddresses

/-- info: 'Compilatrix.IxIR1.Readdress.dupVals_success_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.dupVals_success_preimage

/-- info: 'Compilatrix.IxIR1.Readdress.dropVal_success_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.dropVal_success_preimage

/-- info: 'Compilatrix.IxIR1.Readdress.runOp_success_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.runOp_success_preimage

/-- info: 'Compilatrix.IxIR1.Sim.rootOwnership_mapAddresses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.rootOwnership_mapAddresses_iff

/-- info: 'Compilatrix.IxIR1.Readdress.runMain_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.runMain_mapAddresses

/-- info: 'Compilatrix.IxIR1.MutualBlock.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.MutualBlock.semanticAudit_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.Readdress.ImageIndex.semanticAudit_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.ImageIndex.semanticAudit_build

/-- info: 'Compilatrix.IxIR1.ReaddressAll.Result.PreparedAudit.semanticAudit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.Result.PreparedAudit.semanticAudit_eq

/-- info: 'Compilatrix.IxIR1.ReaddressAll.Result.PreparedAudit.rebuildSemanticAudit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.Result.PreparedAudit.rebuildSemanticAudit_eq

/-- info: 'Compilatrix.IxIR1.ReaddressAll.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.semanticAudit_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.ReaddressAll.reserved_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.reserved_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.ReaddressAll.rebuildSemanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.rebuildSemanticAudit_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.ReaddressAll.Result.raw_lookup_of_mem_of_rebuildSemanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.Result.raw_lookup_of_mem_of_rebuildSemanticAudit

/-- info: 'Compilatrix.IxIR1.ReaddressAll.Result.declaration_preimage_of_lookup_of_rebuildSemanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.Result.declaration_preimage_of_lookup_of_rebuildSemanticAudit

/-- info: 'Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_rebuild_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_rebuild_eq_ok

/-- info: 'Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.Reachability.runMain_filterEntries_eq_of_validate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reachability.runMain_filterEntries_eq_of_validate

/-- info: 'Compilatrix.IxIR1.Reachability.runMain_run_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reachability.runMain_run_eq

/-- info: 'Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso

/-- info: 'Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso_rel

/-- info: 'Compilatrix.IxIR1.Sim.HeapHistoryIso.of_toHeapIso_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapHistoryIso.of_toHeapIso_rel

/-- info: 'Compilatrix.IxIR1.Sim.runCode_historyIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_historyIso

/-- info: 'Compilatrix.IxIR1.Sim.runCode_abstractEnvironment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_abstractEnvironment

/-- info: 'Compilatrix.IxIR1.Sim.runCode_exactEnvironment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_exactEnvironment_eq

/-- info: 'Compilatrix.IxIR1.Optimizer.Outcome.reclamation_of_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Optimizer.Outcome.reclamation_of_witness

/-- info: 'Compilatrix.IxIR1.Optimizer.reclamation_of_runWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Optimizer.reclamation_of_runWithProducedHPT_eq

/-- info: 'Compilatrix.IxIR1.Optimizer.reclamation_of_runWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Optimizer.reclamation_of_runWithCachedHPT_eq

/-- info: 'Compilatrix.IxIR1.Sim.applyOwnershipContract_of_papSafeDecls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.applyOwnershipContract_of_papSafeDecls

/-- info: 'Compilatrix.IxIR1.Decl.decodePreimage_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Decl.decodePreimage_roundtrip

/-- info: 'Compilatrix.IxIR1.Decl.decodePreimage_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Decl.decodePreimage_canonical

/-- info: 'Compilatrix.IxIR1.Decl.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Decl.preimage_injective

/-- info: 'Compilatrix.IxIR1.MutualBlock.Block.decodePreimage_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.MutualBlock.Block.decodePreimage_roundtrip

/-- info: 'Compilatrix.IxIR1.MutualBlock.Block.decodePreimage_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.MutualBlock.Block.decodePreimage_canonical

/-- info: 'Compilatrix.IxIR1.MutualBlock.Block.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.MutualBlock.Block.preimage_injective

/-- info: 'Compilatrix.IxIR1.resolveAtoms_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.resolveAtoms_length

/-- info: 'Compilatrix.IxIR1.runCode_ret_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runCode_ret_success

/-- info: 'Compilatrix.IxIR1.runCode_letOp_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runCode_letOp_success

/-- info: 'Compilatrix.IxIR1.runOp_pure_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_pure_success

/-- info: 'Compilatrix.IxIR1.runOp_alloc_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_alloc_success

/-- info: 'Compilatrix.IxIR1.runOp_free_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_free_success

/-- info: 'Compilatrix.IxIR1.runOp_fetch_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_fetch_success

/-- info: 'Compilatrix.IxIR1.runOp_reuse_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_reuse_success

/-- info: 'Compilatrix.IxIR1.runOp_dup_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_dup_success

/-- info: 'Compilatrix.IxIR1.runOp_drop_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_drop_success

/-- info: 'Compilatrix.IxIR1.runOp_dropU_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_dropU_success

/-- info: 'Compilatrix.IxIR1.runOp_call_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_call_success

/-- info: 'Compilatrix.IxIR1.runOp_callSelf_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_callSelf_success

/-- info: 'Compilatrix.IxIR1.runOp_papp_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_papp_success

/-- info: 'Compilatrix.IxIR1.runOp_apply_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_apply_success

/-- info: 'Compilatrix.IxIR1.runOp_extern_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_extern_success

/-- info: 'Compilatrix.IxIR1.invoke_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.invoke_success

/-- info: 'Compilatrix.IxIR1.runCode_case_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runCode_case_success

/-- info: 'Compilatrix.IxIR1.Sim.reuse_shared_sound_with_survivors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.reuse_shared_sound_with_survivors

/-- info: 'Compilatrix.IxIR1.Sim.RValIso.eq_of_location_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RValIso.eq_of_location_eq

/-- info: 'Compilatrix.IxIR1.Sim.RValsIso.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RValsIso.refl

/-- info: 'Compilatrix.IxIR1.Sim.RValsIso.eq_of_location_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RValsIso.eq_of_location_eq

/-- info: 'Compilatrix.IxIR1.Sim.RootsIso.permuteRight' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RootsIso.permuteRight

/-- info: 'Compilatrix.IxIR1.Sim.HeapIso.rootOwnership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapIso.rootOwnership

/-- info: 'Compilatrix.IxIR1.Sim.HeapIso.rootOwnershipPreimageAppend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapIso.rootOwnershipPreimageAppend

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.refl

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.trans

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.stepOp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.stepOp

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.caseCtor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.caseCtor

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.caseNatZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.caseNatZero

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.caseNatSucc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.caseNatSucc

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.tailCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.tailCall

/-- info: 'Compilatrix.IxIR1.ExecutionHistory.tailCallSelf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ExecutionHistory.tailCallSelf

/-- info: 'Compilatrix.IxIR1.invoke_of_body_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.invoke_of_body_run

/-- info: 'Compilatrix.IxIR1.runOp_call_of_body_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_call_of_body_run

/-- info: 'Compilatrix.IxIR1.runOp_callSelf_of_body_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_callSelf_of_body_run

/-- info: 'Compilatrix.IxIR1.applyGo_exact_of_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.applyGo_exact_of_invoke

/-- info: 'Compilatrix.IxIR1.applyGo_over_of_invoke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.applyGo_over_of_invoke

/-- info: 'Compilatrix.IxIR1.runOp_apply_exact_of_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_apply_exact_of_invoke

/-- info: 'Compilatrix.IxIR1.runOp_apply_over_of_invoke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_apply_over_of_invoke

/-- info: 'Compilatrix.IxIR1.runOp_immediate_ctx_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_immediate_ctx_eq

/-- info: 'Compilatrix.IxIR1.runOp_apply_erased_ctx_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_apply_erased_ctx_eq

/-- info: 'Compilatrix.IxIR1.runOp_apply_under_ctx_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.runOp_apply_under_ctx_eq
