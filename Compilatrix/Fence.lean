import Compilatrix.Sim
import Compilatrix.IxIR1.Sim
import Compilatrix.IxIR1.Reclamation
import Compilatrix.IxIR1.LowerSim
import Compilatrix.IxIR1.LowerProgress
import Compilatrix.IxIR1.LowerAddressedSim
import Compilatrix.IxIR1.LowerFullyAddressedSim
import Compilatrix.IxIR1.NoReuseAddressed
import Compilatrix.IxIR1.CostInstance
import Compilatrix.IxIR1.CostModel
import Compilatrix.IxIR1.CostTrace
import Compilatrix.IxIR1.LowerMutualAddressedSim
import Compilatrix.IxIR1.LowerMutualAddressedProgress
import Compilatrix.IxIR0.Decode
import Compilatrix.IxIR0.MutualBlock
import Compilatrix.IxIR0.ReaddressSim
import Compilatrix.IxIR0.ProjectionFree
import Compilatrix.IxIR0.DynamicCost
import Compilatrix.IxIR0.ReaddressProjectionSafe
import Compilatrix.IxIR0.ReaddressOracle
import Compilatrix.IxIR0.ReaddressOracleExamples
import Compilatrix.EraseAddressedSim
import Compilatrix.IxIR1.Decode
import Compilatrix.IxIR1.MutualBlock
import Compilatrix.IxIR1.ReaddressAll
import Compilatrix.IxIR1.HPT
import Compilatrix.IxIR1.HPTSound
import Compilatrix.IxIR1.HPTProduce
import Compilatrix.IxIR1.HPTCache
import Compilatrix.IxIR1.HPTCasePrune
import Compilatrix.IxIR1.HPTCasePruneProgram
import Compilatrix.IxIR1.HPTPAPFuse
import Compilatrix.IxIR1.HPTPAPFuseProgram
import Compilatrix.SimInstance
import Compilatrix.UsageSound
import Compilatrix.Ixon.Address
import Compilatrix.Ixon.Const
import Compilatrix.Pipeline

/-!
# Sorry/axiom fence (roadmap M0)

The mechanical fence for the roadmap's M0 "sorry/axiom fence" row: each
flagship theorem's axiom set is pinned with a `#guard_msgs`-checked
`#print axioms`, so `lake build` fails if a `sorryAx` or any new axiom
enters its dependency cone. Pure theorem sets are subsets of the intended
triple `propext`/`Classical.choice`/`Quot.sound`, spelled exactly as
reported (`invoke_fn_result_hasWorld` happens not to use
`Classical.choice`; a pin that widens is as much a diff as one that
breaks). The production content-addressing pins additionally expose the one
native BLAKE3 axiom already inventoried in the trusted-extern ledger; their
generic evaluator-renaming core remains inside the pure set.

The codec proof layer is pinned too: `Address`, `Univ`, `Expr`,
`ConstantInfo`, and `Constant` each contribute their roundtrip and
canonical-decoding laws, while IxIR₀ and IxIR₁ declarations contribute
framed roundtrip, accepted-byte canonicality, and preimage injectivity. The
two cycle-safe block codecs contribute the same three laws. Their proofs use
kernel-checked extensionality and arithmetic, so all twenty-two laws
stay inside the same intended axiom triple.
-/

/-! ## Erasure simulation (`Compilatrix/Sim.lean`) -/

/-- info: 'Compilatrix.Ixon.Eval.projectValue_ok_of_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Eval.projectValue_ok_of_strict

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

/-! ## Usage-checker non-interference (`Compilatrix/UsageSound.lean`)

Pin the generic common-erasure observation theorem, its contentful checked
and certified dropped-variable instance, and the corresponding whole-entry
forward simulation. -/

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

/-! ## IxIR₀ → IxIR₁ lowering soundness (`Compilatrix/IxIR1/Sim.lean`) -/

/-- info: 'Compilatrix.IxIR1.Sim.reuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.reuse_sound

/-- info: 'Compilatrix.IxIR1.Sim.invoke_fn_result_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.invoke_fn_result_hasWorld

/-! ## IxIR₁ reclamation (`Compilatrix/IxIR1/Reclamation.lean`,
`Compilatrix/IxIR1/NoReuse.lean`, and
`Compilatrix/IxIR1/NoReuseAddressed.lean`)

Pin the finite empty-root theorem, the public semantic bridge, the actual
no-`reuse` compiler proof, and its pure address-transport boundary.  The
production SCC corollary additionally carries the already-ledgered native
BLAKE3 audit axiom. -/

/-- info: 'Compilatrix.IxIR1.Reclamation.live_eq_zero_of_empty_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.live_eq_zero_of_empty_roots

/-- info: 'Compilatrix.IxIR1.Reclamation.shared_reclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.shared_reclamation

/-- info: 'Compilatrix.IxIR1.LowerSim.reclamation_of_run_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.reclamation_of_run_invariants

/-- info: 'Compilatrix.IxIR1.LowerSim.reclamation_of_run_ownership_and_zero_reuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.reclamation_of_run_ownership_and_zero_reuses

/-- info: 'Compilatrix.IxIR1.Reclamation.runMain_order_of_reuses_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runMain_order_of_reuses_eq_zero

/-- info: 'Compilatrix.IxIR1.Reclamation.runOp_order_of_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runOp_order_of_reuses_eq

/-- info: 'Compilatrix.IxIR1.NoReuse.runMain_reuses_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.runMain_reuses_eq_zero

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_main_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_main_owned

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

/-! ## IxIR₁ cost refinement (`Compilatrix/IxIR1/LowerSim.lean`,
`Compilatrix/IxIR1/NoReuse.lean`, and
`Compilatrix/IxIR1/NoReuseAddressed.lean`, and
`Compilatrix/IxIR1/CostInstance.lean`, and
`Compilatrix/IxIR1/CostModel.lean`,
`Compilatrix/IxIR0/DynamicCost.lean`,
`Compilatrix/IxIR0/ProjectionFree.lean`, and
`Compilatrix/IxIR1/CostTrace.lean`)

Pin the target-only counter interface, the first concrete whole-pass equation
(`reuses = 0`), both pure and production address transport, and a
nonvacuous exact `(allocs, reuses, frees, rcops) = (1, 0, 0, 0)` compiler
instance.  The general runtime balance additionally pins
`nodes.size = allocs` and `live + frees = allocs`; its counter-facing
consequence is `frees ≤ allocs`.  The parametric unary-constructor fragment
then connects actual whole-pass lowering to the exact source-result equation
`allocs = constructorNodes`, with zero reuse/free/RC traffic.  The dynamic
extension pins additive call/recursor profiles, structural trace recovery for
projection-free executions, and the generic profile-to-counter bridge.  Its
retain-width extension and counter-growth algebra expose the unbounded PAP/
closure dimension needed by a compiler-derived RC tariff; the first runtime
producer bounds `dupVals` by the retained prefix length.  The shared-RC
potential then makes arbitrary recursive shared and unique release locally
free: every shared drop exchanges one outstanding-count unit for one RC
instruction.  The primitive classifier covers every non-recursive append-only
operation and lifts its allowance through identity, operation emission,
emitter composition, and return sealing while preserving allocation order and
environment bounds.  A generic run certificate combines that potential bound
with allocation/reuse facts and the existing heap balance to recover the
public four-counter tariff. -/

/-- info: 'Compilatrix.IxIR1.Reclamation.runMain_nodes_size_eq_allocs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runMain_nodes_size_eq_allocs

/-- info: 'Compilatrix.IxIR1.Reclamation.runMain_live_add_frees_eq_allocs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Reclamation.runMain_live_add_frees_eq_allocs

/-- info: 'Compilatrix.IxIR1.LowerSim.RunCostInvariant.costRefinement' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.RunCostInvariant.costRefinement

/-- info: 'Compilatrix.IxIR1.LowerSim.CostRefinement.and' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CostRefinement.and

/-- info: 'Compilatrix.IxIR1.LowerSim.allocationFreeCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.allocationFreeCostRefinement

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllAction_reuseCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllAction_reuseCostRefinement

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllAction_costRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllAction_costRefinement

/-- info: 'Compilatrix.IxIR1.NoReuse.runCostInvariant_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.runCostInvariant_mapAddresses

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

/-- info: 'Compilatrix.IxIR0.DynamicCost.Eval.ofTrace' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.DynamicCost.Eval.ofTrace

/-- info: 'Compilatrix.IxIR0.DynamicCost.Applies.append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.DynamicCost.Applies.append

/-- info: 'Compilatrix.IxIR0.ProjectionFree.Eval.of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.ProjectionFree.Eval.of_run

/-- info: 'Compilatrix.IxIR1.CostTrace.ProfileCostRefinement.of_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.ProfileCostRefinement.of_witness

/-- info: 'Compilatrix.IxIR0.DynamicCost.Eval.surfaceEvals_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.DynamicCost.Eval.surfaceEvals_le

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

/-- info: 'Compilatrix.IxIR1.LowerSim.papp_graph_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.papp_graph_op

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

/-! ## Whole-pass lowering instance (`Compilatrix/SimInstance.lean`)

The four boundaries the M2b ledger claims for the actual compiled
`add 2̂ 3̂` output: exact ownership contracts, the source-to-target
`ValueGraph` forward simulation, all-fuel memory-error exclusion, and the
call/recursion-sensitive source-profile cost refinement.
Pinning them here is what makes
"without `native_decide`" mechanical rather than editorial. -/

/-- info: 'Compilatrix.SimInstance.addIxIR1CompilerContracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1CompilerContracts

/-- info: 'Compilatrix.SimInstance.addIxIR1SemanticForwardSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1SemanticForwardSimulation

/-- info: 'Compilatrix.SimInstance.addIxIR1MemoryErrorUnreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1MemoryErrorUnreachable

/-- info: 'Compilatrix.SimInstance.addIxIR1DynamicCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1DynamicCostRefinement

/-! ## Generic whole-pass target safety
(`Compilatrix/IxIR1/LowerProgress.lean`) -/

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_memoryErrorUnreachable_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_memoryErrorUnreachable_sealed

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllAction_unknownRefUnreachable_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllAction_unknownRefUnreachable_sealed

/-! ## Content-addressed lowering transport
(`Compilatrix/IxIR1/ReaddressSim.lean`,
`Compilatrix/IxIR1/LowerAddressedSim.lean`)

The generic evaluator proof is independent of hashing.  The production
corollaries consume a successful native BLAKE3 post-pass run, so the exact
native implementation axiom is an intentional, mechanically visible member
of those cones.  Pin the indexed artifact boundary used by `Pipeline` across
identity protection, exact runs, addressed value graphs, all three dynamic
error classes, and cost counters. -/

/-- info: 'Compilatrix.IxIR1.Readdress.evalTransportAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.evalTransportAt

/-- info: 'Compilatrix.IxIR1.Readdress.runMain_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Readdress.runMain_mapAddresses

/-! IxIR₀ now has the corresponding full-value transport: closures,
constructor identities, PAP heads, oracle calls, and address-bearing errors
all commute with the map. -/

/-- info: 'Compilatrix.IxIR0.Readdress.evalTransportAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.evalTransportAt

/-- info: 'Compilatrix.IxIR0.Readdress.Ctx.run_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.Ctx.run_mapAddresses

/-- info: 'Compilatrix.IxIR0.Readdress.ProjectionSafe.Eval.mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.ProjectionSafe.Eval.mapAddresses

/-! The executable oracle view reverse-resolves only declaration keys and
maps returned values forward. Its compatibility theorem remains independent
of hashing; the successful production wrapper below exposes the native hash
boundary used to construct the recorded program map. -/

/-- info: 'Compilatrix.IxIR0.Readdress.Oracle.readdress_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.Oracle.readdress_compatible

/-- info: 'Compilatrix.EraseAddressed.run_readdressOracle_semantics_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.EraseAddressed.run_readdressOracle_semantics_of_run_eq_ok

/-! The cycle-safe IxIR₀ block codec is pure, while successful transient-name
materialization intentionally crosses the same native BLAKE3 boundary. -/

/-- info: 'Compilatrix.IxIR0.MutualBlock.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MutualBlock.semanticAudit_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.MutualBlock.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.MutualBlock.semanticAudit_of_run_eq_ok

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

/-! Checked HPT summaries expose both the untrusted candidate's post-fixpoint
condition and the exact cache/content-address audit. Materialization uses the
same ledgered BLAKE3 boundary as the program artifacts. -/

/-- info: 'Compilatrix.IxIR1.HPT.postFixpoint_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.postFixpoint_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.semanticAudit_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.semanticAudit_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.postFixpoint_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.postFixpoint_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.semanticAudit_of_run_eq_ok

/-! The abstract interpreter's evaluator concretization is pure.  Composing
that theorem with accepted native-addressed certificates exposes exactly the
same ledgered BLAKE3 axiom as the existing post-fixpoint/materialization
boundary, including through the pipeline API. -/

/-! Recursive field refinement itself is hash-independent. These pins cover
the mutually recursive order transport and both directions of the bounded
root/field conversion used by allocation, fetch, and case binders. -/

/-- info: 'Compilatrix.IxIR1.HPT.FieldShape.holds_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldShape.holds_of_le

/-- info: 'Compilatrix.IxIR1.HPT.FieldFact.holds_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFact.holds_of_le

/-- info: 'Compilatrix.IxIR1.HPT.FieldFactsHold.holds_of_listLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFactsHold.holds_of_listLe

/-- info: 'Compilatrix.IxIR1.HPT.HeapShape.toFieldShape_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.HeapShape.toFieldShape_holds

/-- info: 'Compilatrix.IxIR1.HPT.FieldShape.toHeapShape_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldShape.toHeapShape_holds

/-- info: 'Compilatrix.IxIR1.HPT.FieldFact.ofFact_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFact.ofFact_holds

/-- info: 'Compilatrix.IxIR1.HPT.FieldFact.toFact_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFact.toFact_holds

/-- info: 'Compilatrix.IxIR1.HPT.Fact.caseFields_ctor_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.caseFields_ctor_holds

/-- info: 'Compilatrix.IxIR1.HPT.Fact.caseFields_natSucc_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.caseFields_natSucc_holds

/-- info: 'Compilatrix.IxIR1.HPT.analyzeOp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.analyzeOp_sound

/-- info: 'Compilatrix.IxIR1.HPT.invoke_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.invoke_sound

/-- info: 'Compilatrix.IxIR1.HPT.functionSummary_sound_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.functionSummary_sound_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.functionSummary_sound_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.functionSummary_sound_of_run_eq_ok

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

/-! Deterministic production remains outside the trust boundary: its output
stores an equality showing that the ordinary checker accepted it.  These pins
make the resulting post-fixpoint, audit, and evaluator guarantees expose the
same native materialization dependency and nothing further. -/

/-- info: 'Compilatrix.IxIR1.HPT.Production.postFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Production.postFixpoint

/-- info: 'Compilatrix.IxIR1.HPT.Production.semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Production.semanticAudit

/-- info: 'Compilatrix.IxIR1.HPT.Production.functionSummary_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Production.functionSummary_sound

/-- info: 'Compilatrix.Pipeline.Artifact.functionSummary_sound_of_producedHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.functionSummary_sound_of_producedHPT

/-! Persistent-cache hits and artifact-local rebuilds are likewise outside the
trust boundary: the returned value stores the exact ordinary checker equality.
The filesystem adapter carries no theorem and cannot weaken these cones. -/

/-- info: 'Compilatrix.IxIR1.HPT.Cache.Production.postFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Cache.Production.postFixpoint

/-- info: 'Compilatrix.IxIR1.HPT.Cache.Production.semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Cache.Production.semanticAudit

/-- info: 'Compilatrix.IxIR1.HPT.Cache.Production.functionSummary_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Cache.Production.functionSummary_sound

/-- info: 'Compilatrix.Pipeline.Artifact.functionSummary_sound_of_cachedHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.functionSummary_sound_of_cachedHPT

/-! The first HPT consumer, including owner-sensitive whole-function fact
propagation, recursive supplied-code traversal, self-call-aware rewriting, and
declaration-graph rebuilding, is pure through its logical old-keyed layer.
Checked, directly produced, cached, and content-address rebuild wrappers add
exactly the already-ledgered native digest dependency, and no
transformation-specific assumption. -/

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_runWithFacts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_runWithFacts_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_rewriteCurrentAt_body_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_rewriteCurrentAt_body_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq_of_runWith_eq_ok

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

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_runWith_eq_ok

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

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_runWith_eq_ok

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

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_rewriteProgram_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_rewriteProgram_eq

/-- info: 'Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_rebuild_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_rebuild_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram

/-! The first allocation-shrinking consumer is pure through both the generic
heap-history evaluator congruence and its executable local decision theorem. -/

/-- info: 'Compilatrix.IxIR1.Sim.runCode_historyIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_historyIso

/-- info: 'Compilatrix.IxIR1.HPT.PAPFuse.fusePair?_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.PAPFuse.fusePair?_refines

/-- info: 'Compilatrix.IxIR1.Sim.runCode_abstractEnvironment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_abstractEnvironment

/-- info: 'Compilatrix.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle

/-- info: 'Compilatrix.Pipeline.Artifact.runMain_pruneProgram_of_checkAndPruneProgramWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.Artifact.runMain_pruneProgram_of_checkAndPruneProgramWith_eq_ok

/-- info: 'Compilatrix.IxIR0.Readdress.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.semanticAudit_of_run_eq_ok

/-- info: 'Compilatrix.IxIR0.Readdress.isolates_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.isolates_of_run_eq_ok

/-- info: 'Compilatrix.IxIR0.Readdress.Oracle.Readdressable.examples_of_isolates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.Oracle.Readdressable.examples_of_isolates

/-- info: 'Compilatrix.IxIR0.Readdress.Oracle.Readdressable.examples_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.Oracle.Readdressable.examples_of_run_eq_ok

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

/-! The SCC-aware production boundary carries the same native digest axiom
and now permits source-function rekeying while auditing constructor stability. -/

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain

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

/-! ## Erasure-safe whole-pass progress
(`Compilatrix/IxIR1/LowerProgress.lean`)

The certified-erasure route rules out the raw lowering's erased-projection
absorber.  Pin both the source-side projection-safety bridge and the resulting
whole-main progress/simulation boundaries.  The call-aware pins additionally
ensure that callable target progress is reconstructed from exact source-fuel
traces and whole-pass provenance, rather than from `CompilerProgressContracts`.
-/

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

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_with_members

/-- info: 'Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed

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

/-! ## Semantic projection (`Compilatrix/IxIR1/LowerSim.lean`)

The premise-free member of the projection value pipeline: variable-target
projection needs no compiler-induction hypothesis, so its cone is the whole
borrow/fetch/retain/release argument. -/

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerE_proj_var_run_value_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerE_proj_var_run_value_sound

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerE_proj_erasure_run_value_progress_within' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerE_proj_erasure_run_value_progress_within

/-! ## Indexed address environments (`Compilatrix/AddressEnv.lean`)

The corpus path builds each hash index once, while these equalities retain the
transparent first-binding-wins list semantics as the proof specification. -/

/-- info: 'Compilatrix.AddressEnv.lookup_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.AddressEnv.lookup_build

/-- info: 'Compilatrix.IxIR1.Lower.lowerAllIndexed_eq_lowerAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Lower.lowerAllIndexed_eq_lowerAll

/-- info: 'Compilatrix.Pipeline.ResolverIndex.resolve_ofList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ResolverIndex.resolve_ofList

/-! ## Codec laws -/

/-- info: 'Compilatrix.Ixon.Address.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Address.roundtripLaw

/-- info: 'Compilatrix.Ixon.Address.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Address.canonicalLaw

/-- info: 'Compilatrix.Ixon.Univ.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Univ.roundtripLaw

/-- info: 'Compilatrix.Ixon.Univ.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Univ.canonicalLaw

/-- info: 'Compilatrix.Ixon.Expr.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Expr.roundtripLaw

/-- info: 'Compilatrix.Ixon.Expr.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Expr.canonicalLaw

/-- info: 'Compilatrix.Ixon.ConstantInfo.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.ConstantInfo.roundtripLaw

/-- info: 'Compilatrix.Ixon.ConstantInfo.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.ConstantInfo.canonicalLaw

/-- info: 'Compilatrix.Ixon.Constant.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Constant.roundtripLaw

/-- info: 'Compilatrix.Ixon.Constant.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Constant.canonicalLaw

/-- info: 'Compilatrix.IxIR0.Decl.decodePreimage_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Decl.decodePreimage_roundtrip

/-- info: 'Compilatrix.IxIR0.Decl.decodePreimage_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Decl.decodePreimage_canonical

/-- info: 'Compilatrix.IxIR0.Decl.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Decl.preimage_injective

/-- info: 'Compilatrix.IxIR1.Decl.decodePreimage_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Decl.decodePreimage_roundtrip

/-- info: 'Compilatrix.IxIR1.Decl.decodePreimage_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Decl.decodePreimage_canonical

/-- info: 'Compilatrix.IxIR1.Decl.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Decl.preimage_injective

/-- info: 'Compilatrix.IxIR0.MutualBlock.Block.decodePreimage_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MutualBlock.Block.decodePreimage_roundtrip

/-- info: 'Compilatrix.IxIR0.MutualBlock.Block.decodePreimage_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MutualBlock.Block.decodePreimage_canonical

/-- info: 'Compilatrix.IxIR0.MutualBlock.Block.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MutualBlock.Block.preimage_injective

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
