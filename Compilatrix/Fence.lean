import Compilatrix.Sim
import Compilatrix.X86.NatCallsSim
import Compilatrix.UniqueReuse.PipelineSim
import Compilatrix.UniqueReuse.NativeSim
import Compilatrix.UniqueReuse.RuntimeNativeSim
import Compilatrix.UniqueReuse.RuntimeObjectSim
import Compilatrix.X86.RuntimeReject
import Compilatrix.X86.ByteBranch
import Compilatrix.X86.ByteCall
import Compilatrix.X86.StreamExamples
import Compilatrix.IxIR2.CreditRefinement
import Compilatrix.Borrow.Pipeline
import Compilatrix.Borrow.RuntimeSim
import Compilatrix.Borrow.RuntimeInput
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
import Compilatrix.IxIR1.HPTFetchForward
import Compilatrix.IxIR1.HPTDestroy
import Compilatrix.IxIR1.Reachability
import Compilatrix.IxIR1.HPTPAPFuseProgram
import Compilatrix.SimInstance
import Compilatrix.UsageSound
import Compilatrix.Ixon.Address
import Compilatrix.Ixon.Const
import Compilatrix.IxIR2.EvalCounter
import Compilatrix.IxIR2.Lower
import Compilatrix.IxIR2.LowerSim
import Compilatrix.IxIR2.Pipeline
import Compilatrix.IxIR2.PipelineSim
import Compilatrix.IxIR2.LivenessExamples
import Compilatrix.IxIR2.Reuse
import Compilatrix.IxIR2.ReuseSim
import Compilatrix.IxIR2.ReuseLiveSim
import Compilatrix.IxIR2.ReuseSimExamples
import Compilatrix.IxIR2.ReuseExamples
import Compilatrix.X86.Basic
import Compilatrix.X86.Eval
import Compilatrix.X86.EvalExamples
import Compilatrix.X86.Select
import Compilatrix.X86.PipelineSim
import Compilatrix.X86.SelectExamples
import Compilatrix.X86.Encode
import Compilatrix.X86.EncodeExamples
import Compilatrix.X86.ELF
import Compilatrix.X86.ELFExamples
import Compilatrix.Pipeline
import Compilatrix.PipelineSound
import Compilatrix.Recursion.Sim
import Compilatrix.Recursion.PhysicalSim
import Compilatrix.Recursion.Resources
import Compilatrix.Recursion.Allocation
import Compilatrix.Recursion.Costs
import Compilatrix.CallReuse.Sim
import Compilatrix.CallReuse.MapSim

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

/-- info: 'Compilatrix.Ixon.UsageCheck.closureWorld_shared_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.UsageCheck.closureWorld_shared_iff

/-- info: 'Compilatrix.Ixon.UsageCheck.check_lam_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.UsageCheck.check_lam_shared

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

/-- info: 'Compilatrix.IxIR1.Sim.reuse_shared_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.reuse_shared_sound

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

/-- info: 'Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw

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

/-- info: 'Compilatrix.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_exact_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_exact_sealed

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
`Compilatrix/IxIR1/ReaddressOwnership.lean`,
`Compilatrix/IxIR1/LowerAddressedSim.lean`)

The generic evaluator proof is independent of hashing.  The production
corollaries consume a successful native BLAKE3 post-pass run, so the exact
native implementation axiom is an intentional, mechanically visible member
of those cones.  Pin the indexed artifact boundary used by `Pipeline` across
identity protection, exact runs, addressed value graphs, all three dynamic
error classes, and cost counters. -/

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

/-- info: 'Compilatrix.IxIR1.HPT.Fact.exactConstructor?_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.exactConstructor?_eq_some

/-- info: 'Compilatrix.IxIR1.HPT.Fact.exactConstructor?_holds_loc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.exactConstructor?_holds_loc

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

/-- info: 'Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.ReaddressAll.runMain_exact_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram

/-! Scalar fetch forwarding is exact both at one accepted constructor/fetch
pair and through its owner-sensitive recursive traversal. -/

/-- info: 'Compilatrix.IxIR1.HPT.FetchForward.runCode_forwardHead?_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FetchForward.runCode_forwardHead?_eq

/-- info: 'Compilatrix.IxIR1.HPT.FetchForward.runCode_runWithFacts_eq_ownerCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FetchForward.runCode_runWithFacts_eq_ownerCompatible

/-! Shape-specialized destruction is pure at both the accepted local
decision and the complete owner-sensitive fact traversal. -/

/-- info: 'Compilatrix.IxIR1.HPT.Destroy.runOp_specialize?_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Destroy.runOp_specialize?_success

/-- info: 'Compilatrix.IxIR1.HPT.Destroy.runCode_runWithFacts_success_ownerCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Destroy.runCode_runWithFacts_success_ownerCompatible

/-! Rooted reachability is exact after validation and through its fail-soft
produce/check/apply wrapper.  Both public theorems expose the native BLAKE3
axiom because validation commits to the exact input graph digest. -/

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

/-! The first allocation-shrinking consumer is pure through both the generic
heap-history evaluator congruence and its executable local decision theorem. -/

/-- info: 'Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso

/-- info: 'Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapHistoryIso.toHeapIso_rel

/-- info: 'Compilatrix.IxIR1.Sim.HeapHistoryIso.of_toHeapIso_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapHistoryIso.of_toHeapIso_rel

/-- info: 'Compilatrix.IxIR1.Sim.runCode_historyIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_historyIso

/-- info: 'Compilatrix.IxIR1.HPT.PAPFuse.fusePair?_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.PAPFuse.fusePair?_refines

/-- info: 'Compilatrix.IxIR1.Sim.runCode_abstractEnvironment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_abstractEnvironment

/-- info: 'Compilatrix.IxIR1.Sim.runCode_exactEnvironment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.runCode_exactEnvironment_eq

/-- info: 'Compilatrix.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle

/-! Fail-soft optimizer reclamation uses one forwarded execution, evaluator
determinism, allocation-history release transport, and the exact final rebuild.
The produced and cached wrappers expose the same native digest boundary as the
checked HPT and rebuild inputs. -/

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

/-- info: 'Compilatrix.IxIR0.Readdress.Result.declaration_lookup_of_mem_of_semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.Result.declaration_lookup_of_mem_of_semanticAudit

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

/-! The validated pipeline retains the exact member scope, erasure certificate,
member coverage, and both address-pass equations consumed by the production
semantic endpoint.  Its O1 projection pins semantic preservation, progress,
memory-error exclusion, reclamation, and the evaluator-universal allocation/
free law directly on the artifact selected by the fail-soft optimizer. -/

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

/-! ## Owner-sensitive dynamic application

Dynamic PAP entry is guarded by declaration metadata, while saturated direct
calls retain heterogeneous ownership boundaries. These pins keep the computed
metadata, whole-pass provenance, strictly-weaker mixed-mode premise, and joint
contract seal inside the ordinary proof axiom envelope. -/

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

/-- info: 'Compilatrix.IxIR1.Sim.applyOwnershipContract_of_papSafeDecls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.applyOwnershipContract_of_papSafeDecls

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

/-! ## IxIR₂ credit-counter algebra -/

/-- info: 'Compilatrix.IxIR2.Eval.CounterLaw.afterHotReset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CounterLaw.afterHotReset

/-- info: 'Compilatrix.IxIR2.Eval.CounterLaw.afterReuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CounterLaw.afterReuse

/-- info: 'Compilatrix.IxIR2.Eval.CounterLaw.afterDiscard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CounterLaw.afterDiscard

/-- info: 'Compilatrix.IxIR2.Eval.CounterLaw.terminalFrees' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CounterLaw.terminalFrees

/-! ## IxIR₂ structured-lowering acceptance -/

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.headBlock_mem_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.headBlock_mem_blocks

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.blocks_subset_of_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.blocks_subset_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.blocks_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.blocks_subset

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountMatches' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountMatches

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountsMatch' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountsMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountMatches_of_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountMatches_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.entryValueCount_eq_headParams_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.entryValueCount_eq_headParams_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountsMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.entryValueCountsMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.entryValueCountsMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.entryValueCountsMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.inductTree' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.inductTree

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.letOpSyntax_of_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.letOpSyntax_of_match

/-- info: 'Compilatrix.IxIR2.Lower.operationSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.operationSyntax_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.letOpOperationSyntax_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.letOpOperationSyntax_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.retSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.retSyntax_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.tailCallSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.tailCallSyntax_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.tailCallSelfSyntax_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.tailCallSelfSyntax_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.switchSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.switchSyntax_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.syntaxMatches_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.syntaxMatches_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.syntaxMatches' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.syntaxMatches

/-- info: 'Compilatrix.IxIR2.Lower.fetchPrologueAt_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.fetchPrologueAt_of_match

/-- info: 'Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_getElem?

/-- info: 'Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_tag

/-- info: 'Compilatrix.IxIR2.Lower.constructorBranchMatchAt_of_switch_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.constructorBranchMatchAt_of_switch_match

/-- info: 'Compilatrix.IxIR2.Lower.natZeroBranchMatchAt_of_switch_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.natZeroBranchMatchAt_of_switch_match

/-- info: 'Compilatrix.IxIR2.Lower.natBranchPairMatch_of_switch_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.natBranchPairMatch_of_switch_match

/-- info: 'Compilatrix.IxIR2.Lower.switchBranchShape_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.switchBranchShape_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.switchBranchesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.switchBranchesMatch

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantSwitchBranchesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantSwitchBranchesMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.letOpMatch_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.letOpMatch_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.instructionAt_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.instructionAt_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.headBlock_eq_sourceBlock_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.headBlock_eq_sourceBlock_of_match

/-- info: 'Compilatrix.IxIR2.Lower.InputMap.forgets_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.InputMap.forgets_of_check

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.inputMapForgets_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.inputMapForgets_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.inputMapSize_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.inputMapSize_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.instructionsMatch_of_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.instructionsMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.instructionsMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.instructionsMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.inputMapsMatch_of_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.inputMapsMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.inputMapsMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.inputMapsMatch

/-- info: 'Compilatrix.IxIR2.Lower.functionSourceMatch_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.functionSourceMatch_of_match

/-- info: 'Compilatrix.IxIR2.Lower.functionSourceEq_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.functionSourceEq_eq_true_iff

/-- info: 'Compilatrix.IxIR2.Lower.inputEq_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.inputEq_eq_true_iff

/-- info: 'Compilatrix.IxIR2.Lower.functionTraceMatch_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.functionTraceMatch_of_match

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.rootSourceCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.rootSourceCode

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.sourceArity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.sourceArity

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.sourceResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.sourceResult

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.sourcePapSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.sourcePapSafe

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.entryBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.entryBlock

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.entryPc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.entryPc

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.entryValueCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.entryValueCount

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.entryInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.entryInput

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.rootHeadBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.rootHeadBlock

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainOwner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainOwner

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainSource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainSource

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainGenerated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainGenerated

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainArity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainArity

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainRootSourceCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainRootSourceCode

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainEntryInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainEntryInput

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainHeadBlockAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainHeadBlockAt

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainNonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainNonempty

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.blockAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.blockAt

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.blockAt_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.blockAt_of_mem

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.headBlockAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.headBlockAt

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantHeadBlockAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantHeadBlockAt

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantInstructionsMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantInstructionsMatch

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantInputMapsMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantInputMapsMatch

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantEntryValueCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantEntryValueCount

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantSyntaxMatches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantSyntaxMatches

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantOperationSyntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantOperationSyntax

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.generatedNonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.generatedNonempty

/-- info: 'Compilatrix.IxIR2.Lower.FunctionTrace.descendantLetOpMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.FunctionTrace.descendantLetOpMatch

/-- info: 'Compilatrix.IxIR2.Lower.programTraceOrder_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.programTraceOrder_of_match

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.functionTrace_of_source_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.functionTrace_of_source_mem

/-- info: 'Compilatrix.IxIR2.Lower.Checked.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.valid

/-- info: 'Compilatrix.IxIR2.Lower.CheckedRun.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CheckedRun.valid

/-- info: 'Compilatrix.IxIR2.Lower.Sim.resolveAtom_of_envRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.resolveAtom_of_envRel

/-- info: 'Compilatrix.IxIR2.Lower.Sim.resolveAtom_of_envRel_target' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.resolveAtom_of_envRel_target

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.initial' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.initial

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.empty

/-- info: 'Compilatrix.IxIR2.Lower.Sim.CodeStateRel.blockAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.CodeStateRel.blockAt

/-- info: 'Compilatrix.IxIR2.Lower.Sim.CodeStateRel.instructionAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.CodeStateRel.instructionAt

/-- info: 'Compilatrix.IxIR2.Lower.Sim.CodeStateRel.letOpNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.CodeStateRel.letOpNext

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.forget' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.forget

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.forgetTracedValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.forgetTracedValue

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.forgetTracedErased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.forgetTracedErased

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.entry

/-- info: 'Compilatrix.IxIR2.Lower.Sim.functionEntryCodeState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.functionEntryCodeState

/-- info: 'Compilatrix.IxIR2.Lower.Sim.initialMainState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.initialMainState

/-- info: 'Compilatrix.IxIR2.Lower.Sim.initialMainCodeState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.initialMainCodeState

/-- info: 'Compilatrix.IxIR2.Lower.Sim.runMain_eq_initialMainMachine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.runMain_eq_initialMainMachine

/-- info: 'Compilatrix.IxIR2.Lower.Sim.resolveAtom_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.resolveAtom_shift

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.sourceMapOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.sourceMapOf

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.constructorFields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.constructorFields

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_edge_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_edge_transfer

/-- info: 'Compilatrix.IxIR2.Lower.Sim.resolvedAtoms_of_resolveAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.resolvedAtoms_of_resolveAtoms

/-- info: 'Compilatrix.IxIR2.Lower.Sim.resolveAtoms_exists_of_pointwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.resolveAtoms_exists_of_pointwise

/-- info: 'Compilatrix.IxIR2.Lower.Sim.ResolvedAtomsList.getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.ResolvedAtomsList.getElem?

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.of_edge_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.of_edge_arguments

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_edge_transfer_from_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_edge_transfer_from_parent

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EdgeArgsRel.canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EdgeArgsRel.canonical

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_generated_edge_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_generated_edge_transfer

/-- info: 'Compilatrix.IxIR2.Lower.Sim.edgeRuntimeReady_of_envRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.edgeRuntimeReady_of_envRel

/-- info: 'Compilatrix.IxIR2.Eval.Step.move' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.move

/-- info: 'Compilatrix.IxIR2.Lower.Sim.resolveAtoms_of_envRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.resolveAtoms_of_envRel

/-- info: 'Compilatrix.IxIR2.Lower.Sim.resolveAtoms_of_envRel_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.resolveAtoms_of_envRel_target

/-- info: 'Compilatrix.IxIR2.Lower.Sim.atomsRel_of_translateAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.atomsRel_of_translateAtoms

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.bindValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.bindValue

/-- info: 'Compilatrix.IxIR2.Lower.Sim.CodeStateRel.letOpValueNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.CodeStateRel.letOpValueNext

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_pure_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_pure_move

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_pure_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_pure_move

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_pure_move_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_pure_move_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_pure_move_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_pure_move_success_step

/-- info: 'Compilatrix.IxIR2.Eval.Step.alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.alloc

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.alloc' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.alloc

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_alloc

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_alloc_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_alloc_state

/-- info: 'Compilatrix.IxIR2.Eval.Step.pappFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.pappFn

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_papp_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_papp_fn

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_papp_fn_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_papp_fn_state

/-- info: 'Compilatrix.IxIR2.Eval.RetainSharedMany.empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.RetainSharedMany.empty

/-- info: 'Compilatrix.IxIR2.Eval.RetainSharedMany.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.RetainSharedMany.cons

/-- info: 'Compilatrix.IxIR2.Eval.RetainSharedMany.cons_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.RetainSharedMany.cons_inv

/-- info: 'Compilatrix.IxIR2.Eval.ApplyTransfer.erased' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ApplyTransfer.erased

/-- info: 'Compilatrix.IxIR2.Eval.ApplyTransfer.papUnder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ApplyTransfer.papUnder

/-- info: 'Compilatrix.IxIR2.Eval.ApplyTransfer.papFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ApplyTransfer.papFn

/-- info: 'Compilatrix.IxIR2.Eval.ApplyTransfer.papExtern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ApplyTransfer.papExtern

/-- info: 'Compilatrix.IxIR2.Eval.ApplyTransferCase.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ApplyTransferCase.transfer

/-- info: 'Compilatrix.IxIR2.Eval.ApplyTransfer.classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ApplyTransfer.classify

/-- info: 'Compilatrix.IxIR2.Eval.Step.apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.apply

/-- info: 'Compilatrix.IxIR2.Eval.Step.retApplyMore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.retApplyMore

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dupVals_simulates_retainSharedMany' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dupVals_simulates_retainSharedMany

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.empty

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.positiveSharedRC' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.positiveSharedRC

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtom

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtoms

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtomsReverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtomsReverse

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.constructorBranch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.constructorBranch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.natSuccessor' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.natSuccessor

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCode

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOp

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.invoke

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGo

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCodeNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCodeNoReuse

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOpNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOpNoReuse

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.invokeNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.invokeNoReuse

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGoNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGoNoReuse

/-- info: 'Compilatrix.IxIR2.Lower.Sim.PositiveSharedRC.dupVals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.PositiveSharedRC.dupVals

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_prepare

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_erased

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_pap_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_pap_under

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_pap_saturated_enter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_pap_saturated_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_pap_over_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_applyGo_pap_over_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_under

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_saturated_enter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_saturated_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_over_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_apply_pap_over_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_apply_transfer_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_apply_transfer_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_apply_pap_saturated_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_apply_pap_saturated_enter_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_apply_pap_over_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_apply_pap_over_enter_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_ret_apply_more' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_ret_apply_more

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_apply_more_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_apply_more_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.source_runOp_call_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.source_runOp_call_eq

/-- info: 'Compilatrix.IxIR2.Lower.Sim.source_runOp_callSelf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.source_runOp_callSelf_eq

/-- info: 'Compilatrix.IxIR2.Lower.Sim.source_runCode_tail_call_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.source_runCode_tail_call_eq

/-- info: 'Compilatrix.IxIR2.Lower.Sim.source_runCode_tail_callSelf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.source_runCode_tail_callSelf_eq

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_call_fn_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_call_fn_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_call_self_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_call_self_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_tail_call_fn_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_tail_call_fn_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_tail_call_self_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_tail_call_self_enter

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_source_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_call_self_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_call_self_enter_source_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_source_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_tail_call_self_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_tail_call_self_enter_source_state

/-- info: 'Compilatrix.IxIR2.Eval.Steps.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Steps.trans

/-- info: 'Compilatrix.IxIR2.Eval.initialMachine_store_empty' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.initialMachine_store_empty

/-- info: 'Compilatrix.IxIR2.Eval.runFunction_eq_runMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.runFunction_eq_runMachine

/-- info: 'Compilatrix.IxIR2.Eval.runMain_eq_runMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.runMain_eq_runMachine

/-- info: 'Compilatrix.IxIR2.Eval.Steps.runMachine' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Steps.runMachine

/-- info: 'Compilatrix.IxIR2.Eval.Steps.runMachine_halted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Steps.runMachine_halted

/-! The credit-aware evaluator proof seam used by reuse-insertion proofs. -/

/-- info: 'Compilatrix.IxIR2.Eval.CreditLookup.of_getElem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditLookup.of_getElem

/-- info: 'Compilatrix.IxIR2.Eval.CreditTake.of_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditTake.of_lookup

/-- info: 'Compilatrix.IxIR2.Eval.CreditTakeMany.single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditTakeMany.single

/-- info: 'Compilatrix.IxIR2.Eval.ConstructorView.of_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ConstructorView.of_box

/-- info: 'Compilatrix.IxIR2.Eval.ConstructorView.parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ConstructorView.parts

/-- info: 'Compilatrix.IxIR2.Eval.EdgeTransfer.of_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.EdgeTransfer.of_parts

/-- info: 'Compilatrix.IxIR2.Eval.Step.branchCreditPresent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.branchCreditPresent

/-- info: 'Compilatrix.IxIR2.Eval.Step.branchCreditAbsent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.branchCreditAbsent

/-- info: 'Compilatrix.IxIR2.Eval.Step.allocWithAbsent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.allocWithAbsent

/-- info: 'Compilatrix.IxIR2.Eval.Step.allocWithLogical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.allocWithLogical

/-- info: 'Compilatrix.IxIR2.Eval.Step.allocWithPhysical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.allocWithPhysical

/-- info: 'Compilatrix.IxIR2.Eval.Step.discardCreditAbsent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.discardCreditAbsent

/-- info: 'Compilatrix.IxIR2.Eval.Step.discardCreditLogical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.discardCreditLogical

/-- info: 'Compilatrix.IxIR2.Eval.Step.discardCreditPhysical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.discardCreditPhysical

/-- info: 'Compilatrix.IxIR2.Eval.Step.takeUniqueLogical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.takeUniqueLogical

/-- info: 'Compilatrix.IxIR2.Eval.Step.takeUniquePhysical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.takeUniquePhysical

/-- info: 'Compilatrix.IxIR2.Eval.Step.resetSharedLogicalHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.resetSharedLogicalHot

/-- info: 'Compilatrix.IxIR2.Eval.Step.resetSharedPhysicalHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.resetSharedPhysicalHot

/-- info: 'Compilatrix.IxIR2.Eval.Step.resetSharedCold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.resetSharedCold

/-- info: 'Compilatrix.IxIR2.Eval.EdgeTransfer.baseline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.EdgeTransfer.baseline

/-- info: 'Compilatrix.IxIR2.Eval.Step.jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.jump

/-- info: 'Compilatrix.IxIR2.Eval.Step.switchCtor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.switchCtor

/-- info: 'Compilatrix.IxIR2.Eval.Step.switchNatZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.switchNatZero

/-- info: 'Compilatrix.IxIR2.Eval.Step.switchNatSucc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.switchNatSucc

/-- info: 'Compilatrix.IxIR2.Eval.Step.callFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.callFn

/-- info: 'Compilatrix.IxIR2.Eval.Step.callSelf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.callSelf

/-- info: 'Compilatrix.IxIR2.Eval.Step.tailCallFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.tailCallFn

/-- info: 'Compilatrix.IxIR2.Eval.Step.tailCallSelf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.tailCallSelf

/-- info: 'Compilatrix.IxIR2.Eval.Step.tailCallSelfCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.tailCallSelfCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.retResumeCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.retResumeCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.retHaltCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.retHaltCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.retApplyMoreCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.retApplyMoreCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.tailCallFnCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.tailCallFnCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.callFnCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.callFnCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.callSelfCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.callSelfCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.pappFnCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.pappFnCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.pappExternCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.pappExternCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.externCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.externCleared

/-- info: 'Compilatrix.IxIR2.Eval.Step.applyCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.applyCleared

/-- info: 'Compilatrix.IxIR2.Eval.InstructionTransferCase.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.InstructionTransferCase.step

/-- info: 'Compilatrix.IxIR2.Eval.InstructionTransfer.classify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.InstructionTransfer.classify

/-- info: 'Compilatrix.IxIR2.Eval.TerminatorTransferCase.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.TerminatorTransferCase.step

/-- info: 'Compilatrix.IxIR2.Eval.TerminatorTransfer.classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.TerminatorTransfer.classify

/-- info: 'Compilatrix.IxIR2.Eval.StepCase.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.StepCase.step

/-- info: 'Compilatrix.IxIR2.Eval.Step.classify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.classify

/-- info: 'Compilatrix.IxIR2.Eval.Step.retResume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.retResume

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_letOp_continuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_letOp_continuation

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_case_ctor_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_case_ctor_branch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_case_nat_zero_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_case_nat_zero_branch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_case_nat_succ_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_case_nat_succ_branch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_fetch_prologue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_fetch_prologue

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_switch_ctor_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_switch_ctor_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_switch_nat_zero_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_switch_nat_zero_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_switch_nat_succ_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_switch_nat_succ_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_ret_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_ret_resume

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_resume_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_resume_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_return_to_letOp_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_return_to_letOp_state

/-- info: 'Compilatrix.IxIR2.Eval.Step.retHalt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.retHalt

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_ret_halt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_ret_halt

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_halt_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_halt_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_halt_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_ret_halt_success

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_ret_halt_runMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_ret_halt_runMachine

/-- info: 'Compilatrix.IxIR2.Eval.Step.retainShared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.retainShared

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.rcTick' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.rcTick

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_dup_retain_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_dup_retain_scalar

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_dup_retain_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_dup_retain_shared

/-- info: 'Compilatrix.IxIR2.Eval.Step.fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.fetch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_fetch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_fetch_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_fetch_state

/-- info: 'Compilatrix.IxIR2.Eval.Step.releaseShared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.releaseShared

/-- info: 'Compilatrix.IxIR2.Eval.Step.freeUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.freeUnique

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.kill' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.kill

/-- info: 'Compilatrix.IxIR2.Lower.Sim.releaseShared_of_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.releaseShared_of_scalar

/-- info: 'Compilatrix.IxIR2.Lower.Sim.EnvRel.bindErased' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.EnvRel.bindErased

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_scalar

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_free_freeUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_free_freeUnique

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_free_freeUnique_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_free_freeUnique_state

/-- info: 'Compilatrix.IxIR2.Eval.Step.dropUnique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.dropUnique

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropUnique_of_scalar' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropUnique_of_scalar

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_shared_nonunit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_shared_nonunit

/-- info: 'Compilatrix.IxIR2.Lower.Sim.sourceDropMany_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.sourceDropMany_of_scalars

/-- info: 'Compilatrix.IxIR2.Lower.Sim.sourceDropManyU_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.sourceDropManyU_of_scalars

/-- info: 'Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_of_scalars

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropUniqueWork_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropUniqueWork_of_scalars

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar_ctor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar_ctor

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_shared_unit_scalar_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_shared_unit_scalar_ctor

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropUniqueWork_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropUniqueWork_append

/-- info: 'Compilatrix.IxIR2.Lower.Sim.uniqueDropWork_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.uniqueDropWork_simulation

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropUVal_simulates_dropUniqueWork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropUVal_simulates_dropUniqueWork

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropManyU_simulates_dropUniqueWork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropManyU_simulates_dropUniqueWork

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_dropU_dropUnique_recursive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_dropU_dropUnique_recursive

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_dropU_dropUnique_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_dropU_dropUnique_recursive_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_append

/-- info: 'Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_success_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_success_unique

/-- info: 'Compilatrix.IxIR2.Lower.Sim.sharedReleaseWork_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.sharedReleaseWork_simulation

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropVal_simulates_releaseSharedWork' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropVal_simulates_releaseSharedWork

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropMany_simulates_releaseSharedWork' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropMany_simulates_releaseSharedWork

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_recursive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_drop_release_recursive

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_drop_release_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_drop_release_recursive_state

/-- info: 'Compilatrix.IxIR2.Eval.FieldWorlds.of_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.FieldWorlds.of_replicate

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.hasWorld_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.hasWorld_eq_true_iff

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate_of_ownership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate_of_ownership

/-- info: 'Compilatrix.IxIR2.Lower.Sim.CodeStateRel.resultWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.CodeStateRel.resultWorld

/-- info: 'Compilatrix.IxIR2.Lower.ProgramTraceOrder.main_of_mem_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.ProgramTraceOrder.main_of_mem_owner

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.functionTraceSource_eq_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.functionTraceSource_eq_of_match

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_of_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_of_child

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_descendant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_descendant

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.functionCodeScalarLeavesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.functionCodeScalarLeavesMatch

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_of_codeScalarLeavesMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_of_codeScalarLeavesMatch

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_of_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_of_child

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_descendant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_descendant

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.functionCodeExactFetchesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.functionCodeExactFetchesMatch

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_of_codeExactFetchesMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_of_codeExactFetchesMatch

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.mainAnalysisCurrentCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.mainAnalysisCurrentCompatible

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.functionTraceAnalysisCurrentCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.functionTraceAnalysisCurrentCompatible

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.functionTraceAnalysisCurrent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.functionTraceAnalysisCurrent

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.exactConstructorAt?_of_fetch_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.exactConstructorAt?_of_fetch_descendant

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.scalarLeafAt?_of_free_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.scalarLeafAt?_of_free_descendant

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.schema_fields_replicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.schema_fields_replicate

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.schema_fields_replicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.schema_fields_replicate

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteFacts?_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteFacts?_next

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_next' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_next

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_alternative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_alternative

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_root

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_main' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_main

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteFacts?_sourceCodeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteFacts?_sourceCodeAt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteFacts?_alternative_of_sourceCodeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteFacts?_alternative_of_sourceCodeAt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_root

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_main' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_main

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_ctor

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natZero

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natSucc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natSucc

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next_of_currentCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next_of_currentCompatible

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_eq_some

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_runtime

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_matches_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.exactConstructorAt?_matches_node

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_eq_some

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_runtime

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_matches_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.scalarLeafAt?_matches_node

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_of_run_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_of_run_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_functionRoot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.sourceCodeAt?_functionRoot

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.functionEntryTraceState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.functionEntryTraceState

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.declarationFunctionEntryTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.declarationFunctionEntryTraceState

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.mainFunctionEntryTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.mainFunctionEntryTraceState

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.functionEntryTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.functionEntryTraceState

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.initialMainTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.initialMainTraceState

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.initialMainSourceOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.initialMainSourceOwnership

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.traceState_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.traceState_next

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.traceState_next_of_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.traceState_next_of_member

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.mainTraceState_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.mainTraceState_next

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_transfer_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_apply_transfer_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_erased_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_apply_erased_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_under_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_under_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_saturated_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_saturated_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_over_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_over_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_success

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_saturated_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_saturated_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_over_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_over_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_under_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_under_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_erased_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_erased_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_call_fn_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_self_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_call_self_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_tail_call_fn_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_self_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_tail_call_self_enter_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_return_to_letOp_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_return_to_letOp_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_halt_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_ret_halt_success

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_pure_move_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_pure_move_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_pure_move_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_pure_move_success_step

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_alloc_checked_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_alloc_checked_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_alloc_checked_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_alloc_checked_success_step

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dup_retain_scalar_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_dup_retain_scalar_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dup_retain_shared_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_dup_retain_shared_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_scalar_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_drop_release_scalar_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_scalar_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_scalar_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_recursive_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_drop_release_recursive_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_papp_fn_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_papp_fn_state

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_fetch_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_fetch_state_of_run_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_free_freeUnique_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_free_freeUnique_state_of_run_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.next

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.constructorChild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.constructorChild

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.natZeroChild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.natZeroChild

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.natSuccChild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.TraceStateRel.natSuccChild

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_switch_ctor_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_switch_ctor_state_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_zero_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_zero_state_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_succ_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_succ_state_hpt

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.hptPostFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.hptPostFixpoint

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.hptLocalPostFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.hptLocalPostFixpoint

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.sidecarDeclarationEnvironment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.sidecarDeclarationEnvironment

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.hptSidecarLocalPostFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.hptSidecarLocalPostFixpoint

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.siteEnvironmentHolds_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.siteEnvironmentHolds_next

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

/-- info: 'Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_map_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_map_fst

/-- info: 'Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_of_find?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.sourceAlternativeAtTag?_of_find?

/-- info: 'Compilatrix.IxIR2.Pipeline.indexedCaseSuccess_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.indexedCaseSuccess_of_run

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.allocationSchema_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.allocationSchema_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.allocationSchemasMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.allocationSchemasMatch

/-- info: 'Compilatrix.IxIR2.Lower.Trace.functionAllocationSchemasMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Trace.functionAllocationSchemasMatch

/-- info: 'Compilatrix.IxIR2.Lower.Checked.allocationSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.allocationSchema

/-- info: 'Compilatrix.IxIR2.Lower.Checked.allocationSchemaFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.allocationSchemaFields

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.allocationPosition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.allocationPosition_of_capabilities_match

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_coordinateMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_coordinateMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.positionMatches_of_positionsMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.positionMatches_of_positionsMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.position_of_positionsMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.position_of_positionsMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.positionsMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.positionsMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.positionsMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.positionsMatch

/-- info: 'Compilatrix.IxIR2.Lower.Trace.functionPositionsMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Trace.functionPositionsMatch

/-- info: 'Compilatrix.IxIR2.Lower.Checked.position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.position

/-- info: 'Compilatrix.IxIR2.Lower.BindingCap.matchesParameter' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.BindingCap.matchesParameter

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.parameterCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.parameterCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.capability_of_parameterCapabilitiesMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.capability_of_parameterCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.owned_of_parameterCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.owned_of_parameterCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.positionParameterCapabilitiesMatch_of_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.positionParameterCapabilitiesMatch_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.positionParameterCapabilities_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.positionParameterCapabilities_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.parameterCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.parameterCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Trace.functionParameterCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Trace.functionParameterCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Checked.ownedParameterCapability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.ownedParameterCapability

/-- info: 'Compilatrix.IxIR2.Lower.Checked.parameterCapability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.parameterCapability

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.pureTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.pureTransition_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.pureCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.pureCapabilitiesMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.pureCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.pureCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Trace.functionPureCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Trace.functionPureCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Checked.pureTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.pureTransition

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.dupTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.dupTransition_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.dupCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.dupCapabilitiesMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.dupCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.dupCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Trace.functionDupCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Trace.functionDupCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Checked.dupTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.dupTransition

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.fetchTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.fetchTransition_of_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.fetchCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.fetchCapabilitiesMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.fetchCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.fetchCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Trace.functionFetchCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Trace.functionFetchCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Checked.fetchTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.fetchTransition

/-- info: 'Compilatrix.IxIR2.Lower.retireOwnerCapabilities?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.retireOwnerCapabilities?_size

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.destructionTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.destructionTransition_of_match

/-- info: 'Compilatrix.IxIR2.Lower.Checked.destructionTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.destructionTransition

/-- info: 'Compilatrix.IxIR2.Lower.consumeCapability?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.consumeCapability?_size

/-- info: 'Compilatrix.IxIR2.Lower.consumeCapabilitiesList?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.consumeCapabilitiesList?_size

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.allocationTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.allocationTransition_of_capabilities_match

/-- info: 'Compilatrix.IxIR2.Lower.Checked.allocationTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.allocationTransition

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.pappTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.pappTransition_of_capabilities_match

/-- info: 'Compilatrix.IxIR2.Lower.Checked.pappTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.pappTransition

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.callTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.callTransition_of_capabilities_match

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.callSelfTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.callSelfTransition_of_capabilities_match

/-- info: 'Compilatrix.IxIR2.Lower.Checked.callTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.callTransition

/-- info: 'Compilatrix.IxIR2.Lower.Checked.callSelfTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.callSelfTransition

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_allocationMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_allocationMatch

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.coordinateMatches_of_allocationMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.coordinateMatches_of_allocationMatch

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.sourceCapability_canConsume_of_allocationMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.sourceCapability_canConsume_of_allocationMatch

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.allocationCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.allocationCapabilitiesMatch_of_child

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.Descendant.allocationCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.Descendant.allocationCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Trace.functionAllocationCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Trace.functionAllocationCapabilitiesMatch

/-- info: 'Compilatrix.IxIR2.Lower.Checked.allocationPosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.allocationPosition

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.empty

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.empty

/-- info: 'Compilatrix.IxIR2.Lower.Sim.rootsForCapabilities_setDead_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.rootsForCapabilities_setDead_perm

/-- info: 'Compilatrix.IxIR2.Lower.Sim.rootsForCapabilities_owned_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.rootsForCapabilities_owned_mem

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.focusOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.focusOwned

/-- info: 'Compilatrix.IxIR2.Lower.PositionTrace.inputReg_of_owned_coordinateMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.PositionTrace.inputReg_of_owned_coordinateMatch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.OwnedInputRegisters.ofCoordinate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.OwnedInputRegisters.ofCoordinate

/-- info: 'Compilatrix.IxIR2.Lower.Sim.BorrowSupport.hasWorld' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.BorrowSupport.hasWorld

/-- info: 'Compilatrix.IxIR2.Lower.Sim.BorrowSupport.monoStore' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.BorrowSupport.monoStore

/-- info: 'Compilatrix.IxIR2.Lower.Sim.BorrowSupport.ofRestricts' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.BorrowSupport.ofRestricts

/-- info: 'Compilatrix.IxIR2.Lower.Sim.BorrowProvenance.hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.BorrowProvenance.hasWorld

/-- info: 'Compilatrix.IxIR2.Lower.Sim.BorrowProvenance.ofRestricts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.BorrowProvenance.ofRestricts

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.move

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.pure

/-- info: 'Compilatrix.IxIR2.Lower.Sim.CapabilityHolds.incRcStore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.CapabilityHolds.incRcStore

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.dup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.dup

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.dup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.dup

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.fetch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.fetch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.fetch

/-- info: 'Compilatrix.IxIR2.Lower.Sim.CapabilityHolds.allocNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.CapabilityHolds.allocNode

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.allocationReadyOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.allocationReadyOwnership

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.alloc

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.alloc

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.papp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.papp

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.papp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.papp

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.drop

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.dropU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.dropU

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.free

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.drop

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.dropU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.dropU

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.free

/-- info: 'Compilatrix.IxIR2.Lower.Sim.RootOwnership_reworldHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.RootOwnership_reworldHead

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.callEntryInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.callEntryInvariant

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.callResultInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.callResultInvariant

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callEntry

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfEntry

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallEntry

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallSelfEntry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallSelfEntry

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.returnRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.returnRoot

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callResult

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfResult

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.hasWorld_of_canConsume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.hasWorld_of_canConsume

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtom_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtom_hasWorld

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtoms_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtoms_hasWorld

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation

/-- info: 'Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation_capabilities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation_capabilities

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_alloc_checked_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_alloc_checked_state

/-- info: 'Compilatrix.IxIR2.Lower.Sim.simulate_traced_alloc_checked_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.simulate_traced_alloc_checked_success_step

/-! The continuation-passing whole-trace worker layer stays on the same
audited attachment boundary.  Its finite-step algebra itself needs only
propositional extensionality; attachment-facing cases additionally inherit
the already fenced checked-hash and HPT dependencies. -/

/-- info: 'Compilatrix.IxIR2.Pipeline.ReachesPost.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.ReachesPost.refl

/-- info: 'Compilatrix.IxIR2.Pipeline.ReachesPost.prepend' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.ReachesPost.prepend

/-- info: 'Compilatrix.IxIR2.Pipeline.ReachesPost.step' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.ReachesPost.step

/-- info: 'Compilatrix.IxIR2.Pipeline.BudgetedReachesPost.prependPreserving' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.BudgetedReachesPost.prependPreserving

/-- info: 'Compilatrix.IxIR2.Pipeline.BudgetedReachesPost.prependFramed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.BudgetedReachesPost.prependFramed

/-- info: 'Compilatrix.IxIR2.Pipeline.successfulTraceSimulationAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.successfulTraceSimulationAt_zero

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.haltReturnHandler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.haltReturnHandler

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_pure_move_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_pure_move_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dup_retain_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_dup_retain_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_fetch_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_fetch_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_free_freeUnique_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_free_freeUnique_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_alloc_checked_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_alloc_checked_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_papp_fn_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_papp_fn_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_fn_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_call_fn_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_self_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_call_self_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_fn_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_tail_call_fn_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_self_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_tail_call_self_cps

/-! Recursive dynamic application composes every return-time dispatcher shape
through the smaller-fuel trace worker. -/

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.functionTrace_of_source_declaration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.functionTrace_of_source_declaration

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.applyMorePlan_of_applyGo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.applyMorePlan_of_applyGo

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_over_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_over_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_over_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_over_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.applyMoreReturnHandler_of_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.applyMoreReturnHandler_of_plan

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.applyMoreReturnHandler_of_applyGo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.applyMoreReturnHandler_of_applyGo

/-! The validated raw ownership contract crosses final readdressing for the
exact heap image generated by compiled executions. Syntax reflection and the
worker's `SourceStoreImage` invariant retain that image through every source
operation and PAP-entry intermediate, so no arbitrary-final-heap contract is
exposed by the end-to-end interface. -/

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulationSourceContext_eq_addressedCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulationSourceContext_eq_addressedCtx

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.sourceContextRenames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.sourceContextRenames

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.rawApplyOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.rawApplyOwnership

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.applyGo_exactImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.applyGo_exactImage

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.sourceRebuildSemanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.sourceRebuildSemanticAudit

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.sourceCodeAddressImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.sourceCodeAddressImage

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.runOp_preservesSourceStoreImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.runOp_preservesSourceStoreImage

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations

/-! Exact path-local HPT case facts are checked against emitted constructor
targets and reconstruct the runtime switch selection inside the attachment. -/

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.exactCaseTarget_of_switch_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.exactCaseTarget_of_switch_descendant

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_exactHPT_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_exactHPT_nonempty

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_exactHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_exactHPT

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_exactHPT_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_exactHPT_runtime

/-! Recursive heap traversal is framed by the continuation's independently
selected suffix budget. -/

/-- info: 'Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_add_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.releaseSharedWork_add_suffix

/-- info: 'Compilatrix.IxIR2.Lower.Sim.releaseShared_add_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.releaseShared_add_suffix

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropUniqueWork_add_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropUniqueWork_add_suffix

/-- info: 'Compilatrix.IxIR2.Lower.Sim.dropUnique_add_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.dropUnique_add_suffix

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_recursive_state_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_drop_release_recursive_state_framed

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_recursive_state_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_recursive_state_framed

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_drop_release_cps

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_cps

/-! The exhaustive attached worker and whole-main endpoint stay within the
same explicit native-hash trust boundary as the checked attachment. -/

/-- info: 'Compilatrix.IxIR2.Pipeline.Sidecars.SourceConstructorsValid.runOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Sidecars.SourceConstructorsValid.runOp

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.runOp_preservesSourceStoreImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.runOp_preservesSourceStoreImage

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_residual_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_residual_nonempty

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_residual

/-- info: 'Compilatrix.IxIR2.Lower.Artifact.mainTraceMember' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Artifact.mainTraceMember

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.simulate_traced_letOp_cps_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.simulate_traced_letOp_cps_of_run

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulTraceSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.successfulTraceSimulation

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.successfulMainSimulation

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.sourceContextNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.sourceContextNoReuse

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.pappSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.pappSafe

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulSimulationContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.successfulSimulationContracts

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulCanonicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.successfulCanonicalMainSimulation

/-! ## Checked block-local liveness

The liveness checker retains its accepted coverage equation, and its public
projections turn that equation into per-use coverage and a no-later-use fact.
The executable fixture's proof wrapper must remain reflection-axiom free. -/

/-- info: 'Compilatrix.IxIR2.Liveness.CheckedBlock.coversAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Liveness.CheckedBlock.coversAt

/-- info: 'Compilatrix.IxIR2.Liveness.CheckedBlock.no_use_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Liveness.CheckedBlock.no_use_after

/-- info: 'Compilatrix.IxIR2.Liveness.Examples.registerTwoNoUseAfter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Liveness.Examples.registerTwoNoUseAfter

/-- info: 'Compilatrix.IxIR2.Liveness.Examples.CheckedSuite.accepted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Liveness.Examples.CheckedSuite.accepted

/-! ## Validator-gated dynamic shared reuse insertion

The first compiler-emitted reversal rewrite retains ordinary validation
witnesses for both sides.  Its bounded benchmark checker packages the exact
executed source/baseline/logical/physical Boolean without reflection axioms. -/

/-- info: 'Compilatrix.IxIR2.Reuse.Placement.noUseAfter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Placement.noUseAfter

/-- info: 'Compilatrix.IxIR2.Reuse.inferPlacementWith_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.inferPlacementWith_sound

/-- info: 'Compilatrix.IxIR2.Reuse.representation?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.representation?_sound

/-- info: 'Compilatrix.IxIR2.Reuse.reuseShape?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.reuseShape?_sound

/-- info: 'Compilatrix.IxIR2.Reuse.candidate?_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.candidate?_sound

/-- info: 'Compilatrix.IxIR2.Reuse.Site.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.fits

/-- info: 'Compilatrix.IxIR2.Reuse.Site.placementCoordinates' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.placementCoordinates

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noUseAfter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noUseAfter

/-- info: 'Compilatrix.IxIR2.Reuse.Site.instructionCases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.instructionCases

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noCall

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noCallSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noCallSelf

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noApply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noApply

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noMove

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noFreeUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noFreeUnique

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noPapp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noPapp

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noDropUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noDropUnique

/-- info: 'Compilatrix.IxIR2.Reuse.Site.noAllocUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.noAllocUnique

/-- info: 'Compilatrix.IxIR2.Reuse.Site.ne_resetBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.ne_resetBlock

/-- info: 'Compilatrix.IxIR2.Reuse.Site.candidateCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.candidateCore

/-- info: 'Compilatrix.IxIR2.Reuse.Site.candidateVectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.candidateVectors

/-- info: 'Compilatrix.IxIR2.Reuse.Site.resetBlock_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.resetBlock_eq

/-- info: 'Compilatrix.IxIR2.Reuse.Site.creditBlock_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.creditBlock_eq

/-- info: 'Compilatrix.IxIR2.Reuse.Site.schemas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.schemas

/-- info: 'Compilatrix.IxIR2.Reuse.Site.runtimeSchemas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.runtimeSchemas

/-- info: 'Compilatrix.IxIR2.Reuse.Site.allocationArgumentsFound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.allocationArgumentsFound

/-- info: 'Compilatrix.IxIR2.Reuse.Site.tailArgumentsFound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Site.tailArgumentsFound

/-- info: 'Compilatrix.IxIR2.Reuse.Output.sourceValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Output.sourceValid

/-- info: 'Compilatrix.IxIR2.Reuse.Output.targetValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Output.targetValid

/-- info: 'Compilatrix.IxIR2.Reuse.FunctionRewrite.decisionAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.FunctionRewrite.decisionAt

/-- info: 'Compilatrix.IxIR2.Reuse.FunctionRewrite.acceptedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.FunctionRewrite.acceptedAt

/-- info: 'Compilatrix.IxIR2.Reuse.FunctionRewrite.accepted_target_ne_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.FunctionRewrite.accepted_target_ne_source

/-- info: 'Compilatrix.IxIR2.Reuse.DeclarationDecisions.related' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.DeclarationDecisions.related

/-- info: 'Compilatrix.IxIR2.Reuse.DeclarationsRel.find?_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.DeclarationsRel.find?_fn

/-- info: 'Compilatrix.IxIR2.Reuse.Trace.context_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Trace.context_fn

/-- info: 'Compilatrix.IxIR2.Reuse.Output.trace_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Output.trace_target

/-- info: 'Compilatrix.IxIR2.Reuse.Output.trace_report' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Output.trace_report

/-- info: 'Compilatrix.IxIR2.ReuseSim.translateRegister?_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.translateRegister?_range

/-- info: 'Compilatrix.IxIR2.ReuseSim.ValuesRel.pushResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.ValuesRel.pushResult

/-- info: 'Compilatrix.IxIR2.ReuseSim.valuesRel_helperEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.valuesRel_helperEntry

/-- info: 'Compilatrix.IxIR2.ReuseSim.valuesRel_afterAllocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.valuesRel_afterAllocation

/-- info: 'Compilatrix.IxIR2.ReuseSim.helperEntryValues_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.helperEntryValues_size

/-- info: 'Compilatrix.IxIR2.ReuseSim.branchValues_resolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.branchValues_resolve

/-- info: 'Compilatrix.IxIR2.ReuseSim.helperEdgeTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.helperEdgeTransfer

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAtom_translate' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAtom_translate

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAtoms_translate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAtoms_translate

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAllocationArguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAllocationArguments

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveTailArguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveTailArguments

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotLogicalControlPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotLogicalControlPrefix

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPhysicalControlPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPhysicalControlPrefix

/-- info: 'Compilatrix.IxIR2.ReuseSim.coldControlPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.coldControlPrefix

/-- info: 'Compilatrix.IxIR2.ReuseSim.absentHelperControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.absentHelperControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.logicalPresentHelperControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.logicalPresentHelperControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.physicalPresentHelperControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.physicalPresentHelperControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotReuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotReuse_sound

/-- info: 'Compilatrix.IxIR2.ReuseSim.coldPrefix_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.coldPrefix_commutes

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPrefix_contents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPrefix_contents

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPrefixReuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPrefixReuse_sound

/-- info: 'Compilatrix.IxIR1.Sim.reuse_shared_sound_with_survivors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.reuse_shared_sound_with_survivors

/-- info: 'Compilatrix.IxIR2.ReuseSim.PlannerValueRelevant' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.PlannerValueRelevant

/-- info: 'Compilatrix.IxIR2.ReuseSim.PlannerAtomRelevant' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.PlannerAtomRelevant

/-- info: 'Compilatrix.IxIR2.ReuseSim.PlannerValueInRoots' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.PlannerValueInRoots

/-- info: 'Compilatrix.IxIR2.ReuseSim.MappedValuesInRoots.selfRelated' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.MappedValuesInRoots.selfRelated

/-- info: 'Compilatrix.IxIR2.ReuseSim.ValuesRel.toTranslatedValuesIso' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.ValuesRel.toTranslatedValuesIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.TranslatedValuesIso.pushResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.TranslatedValuesIso.pushResult

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAtom_translate_iso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAtom_translate_iso

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAtoms_translate_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAtoms_translate_iso

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAtom_iso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAtom_iso

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAtoms_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAtoms_iso

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveAllocationArguments_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveAllocationArguments_iso

/-- info: 'Compilatrix.IxIR2.ReuseSim.resolveTailArguments_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.resolveTailArguments_iso

/-- info: 'Compilatrix.IxIR2.ReuseSim.translatedValuesIso_helperEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.translatedValuesIso_helperEntry

/-- info: 'Compilatrix.IxIR2.ReuseSim.translatedValuesIso_afterAllocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.translatedValuesIso_afterAllocation

/-- info: 'Compilatrix.IxIR2.ReuseSim.evalRuntimeSchemas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.evalRuntimeSchemas

/-- info: 'Compilatrix.IxIR2.ReuseSim.physicalPresentHelperControlIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.physicalPresentHelperControlIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPhysicalAcceptedControlIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPhysicalAcceptedControlIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.physicalPresentHelperControlTranslated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.physicalPresentHelperControlTranslated

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPhysicalAcceptedControlTranslated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPhysicalAcceptedControlTranslated

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotLogicalAcceptedControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotLogicalAcceptedControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.coldAcceptedControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.coldAcceptedControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.fetchPrefixControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.fetchPrefixControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.retainPrefixControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.retainPrefixControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.baselineAcceptedControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.baselineAcceptedControl

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotReuse_sound_with_survivors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotReuse_sound_with_survivors

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPrefixReuse_sound_with_survivors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPrefixReuse_sound_with_survivors

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPrefixReuse_sound_under_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPrefixReuse_sound_under_iso

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotLogicalAcceptedPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotLogicalAcceptedPrefix

/-- info: 'Compilatrix.IxIR2.ReuseSim.coldAcceptedPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.coldAcceptedPrefix

/-- info: 'Compilatrix.IxIR2.ReuseSim.hotPhysicalAcceptedPrefixIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.hotPhysicalAcceptedPrefixIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedHotLogicalSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedHotLogicalSimulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedColdSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedColdSimulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedHotPhysicalSimulationIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedHotPhysicalSimulationIso

/-! The whole-program lift keeps its structural lookup, evaluator transport,
heap congruence, and stable lockstep interfaces inside the ordinary logical
axiom envelope. -/

/-- info: 'Compilatrix.IxIR1.Sim.RValIso.eq_of_location_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RValIso.eq_of_location_eq

/-- info: 'Compilatrix.IxIR1.Sim.RValsIso.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RValsIso.refl

/-- info: 'Compilatrix.IxIR1.Sim.RValsIso.eq_of_location_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RValsIso.eq_of_location_eq

/-- info: 'Compilatrix.IxIR2.Eval.FieldWorlds.to_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.FieldWorlds.to_replicate

/-- info: 'Compilatrix.IxIR2.Eval.FieldWorlds.congrStore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.FieldWorlds.congrStore

/-- info: 'Compilatrix.IxIR2.Eval.FieldValuesWorldEq.length_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.FieldValuesWorldEq.length_eq

/-- info: 'Compilatrix.IxIR2.Eval.FieldWorlds.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.FieldWorlds.transport

/-- info: 'Compilatrix.IxIR2.Eval.ConstructorView.congrStore' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ConstructorView.congrStore

/-- info: 'Compilatrix.IxIR2.Eval.ScalarOracleCall.congrOracle' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ScalarOracleCall.congrOracle

/-- info: 'Compilatrix.IxIR2.Eval.ScalarOracleCall.scalar' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.ScalarOracleCall.scalar

/-- info: 'Compilatrix.IxIR2.Eval.CreditLookup.congrDefinition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditLookup.congrDefinition

/-- info: 'Compilatrix.IxIR2.Eval.CreditTake.congrDefinition' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditTake.congrDefinition

/-- info: 'Compilatrix.IxIR2.Eval.CreditTake.target_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditTake.target_eq

/-- info: 'Compilatrix.IxIR2.Eval.CreditTakeMany.definition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditTakeMany.definition

/-- info: 'Compilatrix.IxIR2.Eval.CreditTakeMany.sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditTakeMany.sequence

/-- info: 'Compilatrix.IxIR2.Eval.CreditTakeSequence.toMany' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CreditTakeSequence.toMany

/-- info: 'Compilatrix.IxIR2.Eval.EdgeTransfer.parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.EdgeTransfer.parts

/-- info: 'Compilatrix.IxIR2.Eval.EdgeTransfer.congrDefinition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.EdgeTransfer.congrDefinition

/-- info: 'Compilatrix.IxIR2.Eval.EdgeTransfer.targetBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.EdgeTransfer.targetBlock

/-- info: 'Compilatrix.IxIR2.Eval.EdgeTransfer.definition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.EdgeTransfer.definition

/-- info: 'Compilatrix.IxIR2.Eval.Step.deterministic' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.deterministic

/-- info: 'Compilatrix.IxIR2.Eval.Steps.cancelPrefixToHalted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Steps.cancelPrefixToHalted

/-- info: 'Compilatrix.IxIR2.Eval.Step.extern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.extern

/-- info: 'Compilatrix.IxIR2.Reuse.Decision.replacement_valueParams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Decision.replacement_valueParams

/-- info: 'Compilatrix.IxIR2.Reuse.Decision.replacement_creditParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Decision.replacement_creditParams

/-- info: 'Compilatrix.IxIR2.Reuse.FunctionRewrite.blockCase' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.FunctionRewrite.blockCase

/-- info: 'Compilatrix.IxIR2.Reuse.FunctionRewrite.blockCaseOfLookup' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.FunctionRewrite.blockCaseOfLookup

/-- info: 'Compilatrix.IxIR2.Reuse.FunctionRewrite.targetBlockAbi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.FunctionRewrite.targetBlockAbi

/-- info: 'Compilatrix.IxIR2.Reuse.FunctionRewrite.definition_blocks_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.FunctionRewrite.definition_blocks_nonempty

/-- info: 'Compilatrix.IxIR2.Reuse.Trace.context_extern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Trace.context_extern

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.rvalHasWorld_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.rvalHasWorld_eq

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds_iff

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.constructorView' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.constructorView

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.retainShared' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.retainShared

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.retainSharedMany' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.retainSharedMany

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.reserve' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.reserve

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.tickResetAttempt' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.tickResetAttempt

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.tickHotReset' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.tickHotReset

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.tickColdReset' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.tickColdReset

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseReservation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseReservation

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.reuseReservation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.reuseReservation

/-- info: 'Compilatrix.IxIR2.ReuseSim.heapIsoKillShared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.heapIsoKillShared

/-- info: 'Compilatrix.IxIR2.ReuseSim.heapIsoKillShared_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.heapIsoKillShared_rel

/-- info: 'Compilatrix.IxIR2.ReuseSim.heapIso_rvalHasWorld_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.heapIso_rvalHasWorld_eq

/-- info: 'Compilatrix.IxIR2.ReuseSim.heapIso_fieldWorlds_of_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.heapIso_fieldWorlds_of_replicate

/-- info: 'Compilatrix.IxIR2.ReuseSim.FieldWorlds.avoidsMissing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.FieldWorlds.avoidsMissing

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseShared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseShared

/-- info: 'Compilatrix.IxIR2.ReuseSim.releaseSharedWork_addFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.releaseSharedWork_addFuel

/-- info: 'Compilatrix.IxIR2.ReuseSim.releaseSharedWork_remaining_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.releaseSharedWork_remaining_le

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseSharedWork_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseSharedWork_of_le

/-- info: 'Compilatrix.IxIR2.ReuseSim.releaseShared_remaining_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.releaseShared_remaining_le

/-- info: 'Compilatrix.IxIR2.ReuseSim.releaseShared_addFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.releaseShared_addFuel

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseShared_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.releaseShared_of_le

/-- info: 'Compilatrix.IxIR2.ReuseSim.dropUniqueWork_contents_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.dropUniqueWork_contents_congr

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.dropUnique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.dropUnique

/-- info: 'Compilatrix.IxIR2.ReuseSim.dropUniqueWork_addFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.dropUniqueWork_addFuel

/-- info: 'Compilatrix.IxIR2.ReuseSim.dropUniqueWork_remaining_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.dropUniqueWork_remaining_le

/-- info: 'Compilatrix.IxIR2.ReuseSim.dropUnique_addFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.dropUnique_addFuel

/-- info: 'Compilatrix.IxIR2.ReuseSim.HeapContentsEq.dropUnique_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.HeapContentsEq.dropUnique_of_le

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.entry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.entry

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.atPosition' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.atPosition

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.blockCase' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.blockCase

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.advancePush' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.advancePush

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.push' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.push

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.advance' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.advance

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.advanceAppendCredit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.advanceAppendCredit

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.values_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.values_eq

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.rewritten_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.rewritten_eq

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.advanceTake' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.advanceTake

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.edgeTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.edgeTransfer

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.takeIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.takeIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.takeManyIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.takeManyIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.edgeTransferIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.edgeTransferIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameRel.entry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameRel.entry

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameRel.push' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameRel.push

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameIso.transportRelation

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableFrameRel.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableFrameRel.transportRelation

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableContinuationIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableContinuationIso.transportRelation

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableStackIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableStackIso.transportRelation

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableControlIso.recursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableControlIso.recursiveCall

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMachineRel.contentsRecursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMachineRel.contentsRecursiveCall

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMachineRel.isomorphicRecursiveCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMachineRel.isomorphicRecursiveCall

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableContinuationIso.applyMoreOrResume' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableContinuationIso.applyMoreOrResume

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedHotLogicalStableSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedHotLogicalStableSimulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedColdStableSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedColdStableSimulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedHotPhysicalStableSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedHotPhysicalStableSimulationIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferErased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferErased

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferPapUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferPapUnder

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferPapFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferPapFn

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferPapExtern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedApplyTransferPapExtern

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedApplyTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedApplyTransfer

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedApplyStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedApplyStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedApplyStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedApplyStepOfTrace

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedRetApplyMoreStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedRetApplyMoreStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedRetApplyMoreStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedRetApplyMoreStepOfTrace

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedMoveStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedMoveStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedFetchStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedFetchStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedFreeUniqueStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedFreeUniqueStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedAllocStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedAllocStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedAllocWithAbsentStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedAllocWithAbsentStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedAllocWithLogicalStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedAllocWithLogicalStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedAllocWithPhysicalStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedAllocWithPhysicalStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedDiscardCreditAbsentStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedDiscardCreditAbsentStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedDiscardCreditLogicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedDiscardCreditLogicalStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedDiscardCreditPhysicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedDiscardCreditPhysicalStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedTakeUniqueLogicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedTakeUniqueLogicalStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedTakeUniquePhysicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedTakeUniquePhysicalStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedResetSharedLogicalHotStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedResetSharedLogicalHotStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedResetSharedPhysicalHotStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedResetSharedPhysicalHotStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedResetSharedColdStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedResetSharedColdStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedCallSelfStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedCallSelfStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedCallFnStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedCallFnStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedPappFnStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedPappFnStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedPappExternStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedPappExternStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedExternStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedExternStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedTailCallSelfStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedTailCallSelfStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedTailCallFnStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedTailCallFnStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedRetResumeStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedRetResumeStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedRetHaltStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedRetHaltStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedJumpStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedJumpStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedSwitchCtorStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedSwitchCtorStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedSwitchNatZeroStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedSwitchNatZeroStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedSwitchNatSuccStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedSwitchNatSuccStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedBranchCreditPresentStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedBranchCreditPresentStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedBranchCreditAbsentStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedBranchCreditAbsentStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedRetainSharedStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedRetainSharedStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedReleaseSharedStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedReleaseSharedStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedDropUniqueStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedDropUniqueStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedInstructionStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedInstructionStepOfTrace

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedInstructionStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedInstructionStepOfTraceIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedTerminatorStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedTerminatorStepOfTrace

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedTerminatorStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedTerminatorStepOfTraceIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedStepOfTrace

/-- info: 'Compilatrix.IxIR2.ReuseSim.unchangedStepOfTraceIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.unchangedStepOfTraceIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMacroSimulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMacroSimulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMacroSimulation.ofStepsOne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMacroSimulation.ofStepsOne

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMachineRel.haltedParts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMachineRel.haltedParts

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMacroInvariantStep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMacroInvariantStep

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMacroInvariantStep.simulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMacroInvariantStep.simulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableMacroSimulation.preserveInvariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableMacroSimulation.preserveInvariant

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedHotLogicalStableMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedHotLogicalStableMacroSimulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedColdStableMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedColdStableMacroSimulation

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedHotPhysicalStableMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedHotPhysicalStableMacroSimulationIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.acceptedColdStableMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.acceptedColdStableMacroSimulationIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.stableMacroStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.stableMacroStepOfTrace

/-- info: 'Compilatrix.IxIR2.ReuseSim.stableMacroStepOfTraceIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.stableMacroStepOfTraceIso

/-- info: 'Compilatrix.IxIR2.ReuseSim.stableMacroStepOfTraceRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.stableMacroStepOfTraceRel

/-- info: 'Compilatrix.IxIR2.ReuseSim.stableFiniteExecutionOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.stableFiniteExecutionOfMacroInvariant

/-- info: 'Compilatrix.IxIR2.ReuseSim.stableRunMachineOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.stableRunMachineOfMacroInvariant

/-! ## Liveness-indexed reuse/compiler attachment -/

/-- info: 'Compilatrix.IxIR2.Liveness.instruction_reg_mem_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Liveness.instruction_reg_mem_blockUses

/-- info: 'Compilatrix.IxIR2.Liveness.terminator_reg_mem_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Liveness.terminator_reg_mem_blockUses

/-- info: 'Compilatrix.IxIR2.Liveness.mem_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Liveness.mem_blockUses

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.callRemainingHolds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.callRemainingHolds

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyRemainingHolds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyRemainingHolds

/-- info: 'Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyInputOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyInputOwnership

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AtomLiveFrom.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AtomLiveFrom.mono

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AtomLiveFrom.instruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AtomLiveFrom.instruction

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AtomLiveFrom.terminator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AtomLiveFrom.terminator

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AtomsLiveFrom.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AtomsLiveFrom.mono

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.plannerValueLiveAtAllocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.plannerValueLiveAtAllocation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.plannerValueLiveAtEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.plannerValueLiveAtEntry

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterCases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterCases

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.ofRValsIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.ofRValsIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.advance' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.advance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.mono

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.push

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.append

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtom

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtoms

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.ofStable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.ofStable

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.advance' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.advance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.takeManyIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.takeManyIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.edgeTransferIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.edgeTransferIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.transportRelation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationAvoids.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationAvoids.transportRelation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackAvoids.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackAvoids.transportRelation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableContinuationIso.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableContinuationIso.toLive

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableStackIso.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableStackIso.toLive

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AcceptedPrefixInstruction' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AcceptedPrefixInstruction

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AcceptedPrefixInstructionAt' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AcceptedPrefixInstructionAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.AcceptedEntry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.AcceptedEntry

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPcZero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPcZero

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.halted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.halted

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSameBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSameBlock

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSourceBlockExcluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSourceBlockExcluded

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallResume

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallSelfResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallSelfResume

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofApplyResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofApplyResume

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofMoveAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofMoveAdvance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofFreeUniqueAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofFreeUniqueAdvance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPappAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPappAdvance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofDropUniqueAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofDropUniqueAdvance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofAllocUniqueAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofAllocUniqueAdvance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.valuesAtEntry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.valuesAtEntry

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableMachineRel.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableMachineRel.toLive

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveControlIso.recursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveControlIso.recursiveCall

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel.contentsRecursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel.contentsRecursiveCall

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel.isomorphicRecursiveCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel.isomorphicRecursiveCall

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedMoveStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedMoveStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedFetchStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedFetchStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedFetchPrologueStepsLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedFetchPrologueStepsLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedCallSelfStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedCallSelfStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedCallFnStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedCallFnStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedJumpStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedJumpStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchNatZeroStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchNatZeroStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchNatSuccStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchNatSuccStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchCtorStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchCtorStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchCtorPrologueStepsLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedSwitchCtorPrologueStepsLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedBranchCreditPresentStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedBranchCreditPresentStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedBranchCreditAbsentStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedBranchCreditAbsentStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedTailCallSelfStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedTailCallSelfStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedTailCallFnStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedTailCallFnStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedRetResumeStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedRetResumeStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedRetHaltStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedRetHaltStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AtomsLiveFrom.instruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AtomsLiveFrom.instruction

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationIso.applyMoreOrResumeIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationIso.applyMoreOrResumeIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedFreeUniqueStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedFreeUniqueStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocWithAbsentStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocWithAbsentStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocWithLogicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocWithLogicalStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocWithPhysicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedAllocWithPhysicalStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedTakeUniqueLogicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedTakeUniqueLogicalStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedTakeUniquePhysicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedTakeUniquePhysicalStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedResetSharedLogicalHotStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedResetSharedLogicalHotStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedResetSharedPhysicalHotStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedResetSharedPhysicalHotStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedResetSharedColdStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedResetSharedColdStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedRetainSharedStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedRetainSharedStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedReleaseSharedStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedReleaseSharedStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedDropUniqueStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedDropUniqueStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedDiscardCreditAbsentStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedDiscardCreditAbsentStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedDiscardCreditLogicalStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedDiscardCreditLogicalStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedDiscardCreditPhysicalStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedDiscardCreditPhysicalStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedPappFnStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedPappFnStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedPappExternStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedPappExternStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedExternStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedExternStepLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferErasedLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferErasedLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferPapUnderLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferPapUnderLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferPapFnLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferPapFnLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferPapExternLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferPapExternLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyTransferLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedApplyStepOfTraceLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedRetApplyMoreStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedRetApplyMoreStepOfTraceLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedInstructionStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedInstructionStepOfTraceLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedAcceptedPrefixInstructionStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedAcceptedPrefixInstructionStepOfTraceLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedTerminatorStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedTerminatorStepOfTraceLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedStepOfTraceLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedStepOfTraceLiveIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveSimulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveSimulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveSimulationIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveMacroSimulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccounting

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccountingAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccountingAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIsoAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIsoAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.stableLiveMacroStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.stableLiveMacroStepOfTraceIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt.simulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt.simulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep.simulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep.simulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveInvariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveInvariant

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.ofStepsOne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.ofStepsOne

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableMacroSimulation.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableMacroSimulation.toLive

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfMacroInvariant

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfGuidedMacroInvariant' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfGuidedMacroInvariant

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.stableLiveRunMachineOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.stableLiveRunMachineOfMacroInvariant

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.stableLiveRunMachineOfGuidedMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.stableLiveRunMachineOfGuidedMacroInvariant

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.retainSharedMany_of_rootOwnership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.retainSharedMany_of_rootOwnership

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.retainCtorFields_of_rootOwnership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.retainCtorFields_of_rootOwnership

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.balanceInertRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.balanceInertRoots

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.addInertRoots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.addInertRoots

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.fieldRootPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.fieldRootPartition

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.hotPrefixFieldRootPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.hotPrefixFieldRootPartition

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccounting

/-- info: 'Compilatrix.IxIR1.Sim.RootsIso.permuteRight' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.RootsIso.permuteRight

/-- info: 'Compilatrix.IxIR1.Sim.HeapIso.rootOwnership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapIso.rootOwnership

/-- info: 'Compilatrix.IxIR1.Sim.HeapIso.rootOwnershipPreimageAppend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.HeapIso.rootOwnershipPreimageAppend

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccountingIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccountingIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.ValueSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.ValueSupportedByRoots.mono

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.ValueSupportedByRoots.inBounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.ValueSupportedByRoots.inBounds

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.identityOfInBounds' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.identityOfInBounds

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.identityOfInBounds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.identityOfInBounds

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationIso.identityOfSupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationIso.identityOfSupported

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackIso.identityOfSupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackIso.identityOfSupported

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.ValueSupportedByRoots.avoidsUnitShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.ValueSupportedByRoots.avoidsUnitShared

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameInputCoverage.ofCodeState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameInputCoverage.ofCodeState

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofNoBorrows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofNoBorrows

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSuspension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSuspension

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSelfSuspension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSelfSuspension

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.applyPapEntry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.applyPapEntry

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mono

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesInRoots' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesInRoots

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesAtPlannerAllocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesAtPlannerAllocation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.MappedValuesInRoots.preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.MappedValuesInRoots.preimage

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveContinuationSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveContinuationSupportedByRoots.mono

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveStackSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveStackSupportedByRoots.mono

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfLive

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfSupported

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveFrameIso.toHeapIsoOfSupported

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveContinuationIso.toHeapIsoOfSupported

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackIso.toHeapIsoOfSupported

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackIso.avoidsOfSupportedUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveStackIso.avoidsOfSupportedUnit

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.optimizeAttachment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.optimizeAttachment

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerStackState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerStackState

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerStackReturn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerStackReturn

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerApplyMoreReturn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerApplyMoreReturn

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentOwnership

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.ownedParameterRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.ownedParameterRoot

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRoot

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRootIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRootIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.coverage

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.activeFrameSupportedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.activeFrameSupportedAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.mappedValuesAtPlannerAllocationOfNoBorrows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.mappedValuesAtPlannerAllocationOfNoBorrows

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.withHeapFuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.withHeapFuel

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.compilerStateOfStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.compilerStateOfStep

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixInstructionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixInstructionAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepPure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepPure

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepFetch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepFetch

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepFreeUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepFreeUnique

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainScalar

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainShared

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.allocationReadyOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.allocationReadyOwnership

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.allocationFieldWorlds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.allocationFieldWorlds

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepAlloc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepAlloc

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepPapp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepPapp

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUniqueScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUniqueScalar

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUnique

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseScalar

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseShared

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErased

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.externImpossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.externImpossible

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnder

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapExact

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapOver' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapOver

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentApply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentApply

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.applyInputOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.applyInputOwnership

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.applyPapPreparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.applyPapPreparation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErasedOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErasedOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnderOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnderOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerInstructionCase.resolve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerInstructionCase.resolve

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalInstructionCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalInstructionCase

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalInstructionAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalInstructionAdvance

/-- info: 'Compilatrix.IxIR2.Lower.edgeCapabilities?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.edgeCapabilities?_size

/-- info: 'Compilatrix.IxIR2.Lower.Checked.constructorBranchSchemaArity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.constructorBranchSchemaArity

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase.compilerMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase.compilerMacro

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorCaseOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorCaseOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacroOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacroOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerTerminatorSyntax' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerTerminatorSyntax

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminatorSyntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminatorSyntax

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorCase

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase.resolve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase.resolve

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterBeforeRelease' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterBeforeRelease

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueBound

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueHead

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAtOfFetched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAtOfFetched

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedParameterValueLive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedParameterValueLive

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedCtorChildSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedCtorChildSource

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAtOfParameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAtOfParameters

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAtOfParameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAtOfParameters

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetched

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetchedExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetchedExecution

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.acceptedCtorChildPhysicalMacroOfExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.acceptedCtorChildPhysicalMacroOfExecution

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfCompilerState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfCompilerState

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorAdvanceHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorAdvanceHistory

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterCall

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterCallSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterCallSelf

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCall

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCallSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCallSelf

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatZero

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatSucc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatSucc

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepsSwitchCtor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stepsSwitchCtor

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacro

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnHalt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnHalt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnResume

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMore

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.heap_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.heap_eq

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.heapClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.heapClosed

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteRetainedFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteRetainedFields

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteParameterCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteParameterCount

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.liveValueInBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.liveValueInBounds

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedEntryValueLive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedEntryValueLive

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stackToHeapIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stackToHeapIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.historyOfContents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.historyOfContents

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stackAvoidsOfSupportedUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.stackAvoidsOfSupportedUnit

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteStackAvoidsOfUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteStackAvoidsOfUnit

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistory

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistory

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.initial

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerState

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerMacroStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerMacroStep

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.compilerMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.compilerMacro

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAt

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacro

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.Steps.deterministic' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.Steps.deterministic

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableState

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.simulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.attach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.attach

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistory

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofStepsOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofStepsOne

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.prependStepsOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.prependStepsOne

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofUnchangedSwitchCtorPrologue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofUnchangedSwitchCtorPrologue

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofSwitchCtorChildBlockCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofSwitchCtorChildBlockCase

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfCompilerState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfCompilerState

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.prefixStepOfLetOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.prefixStepOfLetOp

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfPcZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfPcZero

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfHalted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfHalted

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallResume

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallSelfResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallSelfResume

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfApplyResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfApplyResume

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerMacroStep.attach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerMacroStep.attach

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfStep

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfPrefixStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfPrefixStep

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIso

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceRel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceRel

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.invariantStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableMacroStep.invariantStep

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveCompiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveCompiler

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.AttachedStableState.advanceInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.AttachedStableState.advanceInvariant

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableFiniteExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableFiniteExecution

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableFiniteExecutionGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableFiniteExecutionGuided

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableRunMachine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableRunMachine

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedStableRunMachineGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedStableRunMachineGuided

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.MappedValuesInRoots.transportOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.MappedValuesInRoots.transportOwnership

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceFieldCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceFieldCount

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminalAllocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminalAllocation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfExecution

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepOfTraceRelGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepOfTraceRelGuided

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel.rewrittenRunning' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.StableLiveMachineRel.rewrittenRunning

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepGuided

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableFiniteExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableFiniteExecution

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableRunMachine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalStableRunMachine

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.initial

/-- info: 'Compilatrix.IxIR2.ReuseSim.Examples.leafHotReuseProducesRelatedHeaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.Examples.leafHotReuseProducesRelatedHeaps

/-- info: 'Compilatrix.IxIR2.ReuseSim.Examples.linkedHotPrefixProducesRelatedHeaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.Examples.linkedHotPrefixProducesRelatedHeaps

/-- info: 'Compilatrix.IxIR2.Reuse.Examples.CheckedBenchmark.accepted' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Examples.CheckedBenchmark.accepted

/-! ## Typed x86-64 v0 semantic skeleton

The target AST's closed-fragment theorems must remain free of ISA or encoder
assumptions.  The executable local step is likewise an ordinary Lean
definition; its stability theorem stays inside the standard logical fence. -/

/-- info: 'Compilatrix.X86.Instr.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Instr.inV0

/-- info: 'Compilatrix.X86.Terminator.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Terminator.inV0

/-- info: 'Compilatrix.X86.Program.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.Program.inV0

/-- info: 'Compilatrix.X86.Checked.inV0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.Checked.inV0

/-- info: 'Compilatrix.X86.step_of_not_running' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.step_of_not_running

/-- info: 'Compilatrix.X86.Core.applyIntrinsicResult_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Core.applyIntrinsicResult_rsp

/-- info: 'Compilatrix.X86.Core.applyIntrinsicResult_calleeSaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Core.applyIntrinsicResult_calleeSaved

/-! ## First IxIR₂ scalar selection refinement

Successful selector outputs retain their source-validation witness.  The first
physical IxIR₂ move/alias family then refines the System V `rax` leaf result
without adding any ISA, encoder, native-reflection, or FFI axiom. -/

/-- info: 'Compilatrix.X86.Select.Output.sourceValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.Output.sourceValid

/-- info: 'Compilatrix.X86.Select.select_scalarMoveProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.select_scalarMoveProgram

/-- info: 'Compilatrix.X86.Select.scalarMoveRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.scalarMoveRefines

/-- info: 'Compilatrix.X86.Select.selectScalarMoveRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.selectScalarMoveRefines

/-! Source execution history through suspended calls and tail transfers. -/

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

/-- info: 'Compilatrix.IxIR2.Lower.CodeTrace.tailCallResult_of_capabilities_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.CodeTrace.tailCallResult_of_capabilities_match

/-- info: 'Compilatrix.IxIR2.Lower.Checked.tailCallResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Lower.Checked.tailCallResult

/-- info: 'Compilatrix.IxIR2.Pipeline.ApplyMorePlan.sourceRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.ApplyMorePlan.sourceRun

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerStackHistory.advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerStackHistory.advance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerStackHistory.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerStackHistory.complete

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerStackCompletion.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerStackCompletion.ordinary

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.historyStepOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.historyStepOp

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.historyImmediateOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.historyImmediateOp

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnCompletion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnCompletion

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnResumeOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnResumeOfTarget

/-! Residual dispatch, whole-main physical reuse, and checked production selection. -/

/-- info: 'Compilatrix.IxIR2.Eval.runMachine_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.runMachine_steps

/-- info: 'Compilatrix.IxIR2.Reuse.sourceValid_of_invalidTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.sourceValid_of_invalidTarget

/-- info: 'Compilatrix.IxIR2.Reuse.sourceRejected_of_invalidSource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.sourceRejected_of_invalidSource

/-- info: 'Compilatrix.IxIR2.Reuse.Selection.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.Selection.valid

/-- info: 'Compilatrix.IxIR2.Reuse.selectCheckedWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Reuse.selectCheckedWith

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.selectAttachment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.selectAttachment

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreTransfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreTransfer

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreOfTarget

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalCompilerAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.attachedPhysicalCompilerAdvance

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulation

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulation

/-! Baseline interpretation transport and validated source-to-scalar selection. -/

/-- info: 'Compilatrix.IxIR2.CreditFree.instructionAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditFree.instructionAt

/-- info: 'Compilatrix.IxIR2.Eval.runMain_creditFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.runMain_creditFree

/-- info: 'Compilatrix.IxIR2.Eval.runMain_success_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.runMain_success_unique

/-- info: 'Compilatrix.IxIR2.Eval.Steps.addHeapFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Steps.addHeapFuel

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.mainInterpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.mainInterpretation

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.successfulPhysicalMainSimulation

/-- info: 'Compilatrix.X86.Select.ScalarApply.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.ScalarApply.runs

/-- info: 'Compilatrix.X86.Select.sourceWord?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.sourceWord?_sound

/-- info: 'Compilatrix.X86.Select.Output.refinesSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.Output.refinesSuccessfulRun

/-- info: 'Compilatrix.X86.Select.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.sourceRefines

/-- info: 'Compilatrix.X86.Select.sourceScalarRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.Select.sourceScalarRefines

/-! Immediate-list source recursion recovery. The local evaluator theorem
uses the ordinary Lean basis; the addressed wrappers retain the existing
BLAKE3 hash assumption through the canonical derived declaration identity. -/

/-- info: 'Compilatrix.IxIR0.Recursion.sourceTuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Recursion.sourceTuple

/-- info: 'Compilatrix.IxIR0.Recursion.recursorForwardSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Recursion.recursorForwardSimulation

/-- info: 'Compilatrix.IxIR0.Recursion.Recovered.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Recursion.Recovered.forwardSimulation

/-- info: 'Compilatrix.IxIR0.Recursion.Selection.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Recursion.Selection.forwardSimulation

/-- info: 'Compilatrix.Recursion.Compilation.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Compilation.sourceRefines

/-! Common ownership lowering and source recursion through selected physical
execution. These compose the existing addressed compiler and reuse proofs;
the existing BLAKE3 assumption is unchanged. -/

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

/-- info: 'Compilatrix.IxIR0.Recursion.Recovered.projectionSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Recursion.Recovered.projectionSafe

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalMainSimulation

/-- info: 'Compilatrix.Recursion.Lowered.physicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Lowered.physicalMainSimulation

/-- info: 'Compilatrix.Recursion.Compilation.literalSourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Compilation.literalSourceRefines

/-- info: 'Compilatrix.Recursion.Compilation.sourceRefinesSelected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Compilation.sourceRefinesSelected

/-! Physical allocation accounting and selected shared-result reclamation.
The machine and heap-transport lemmas use the ordinary Lean basis; source
composition retains exactly the existing addressed BLAKE3 assumption. -/

/-- info: 'Compilatrix.IxIR2.Eval.Step.allocationAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.allocationAccounting

/-- info: 'Compilatrix.IxIR2.Eval.runMain_allocationAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.runMain_allocationAccounting

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableHeapRel.sharedReclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableHeapRel.sharedReclamation

/-- info: 'Compilatrix.Pipeline.LoweredCompilation.reclamation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.LoweredCompilation.reclamation

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.baselineSharedReclamation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.baselineSharedReclamation

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainResources

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedSuccessfulSharedResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedSuccessfulSharedResources

/-- info: 'Compilatrix.Recursion.Lowered.physicalMainResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Lowered.physicalMainResources

/-- info: 'Compilatrix.Recursion.Compilation.sourceRefinesSelectedWithResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Compilation.sourceRefinesSelectedWithResources

/-! Comparative allocation/free laws. Counters remain separate from the
semantic relations; source composition retains the existing axiom basis. -/

/-- info: 'Compilatrix.IxIR2.Eval.InstructionTransferCase.allocationEvents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.InstructionTransferCase.allocationEvents

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedStep_allocationDelta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedStep_allocationDelta

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableHeapRel.live_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableHeapRel.live_eq

/-- info: 'Compilatrix.IxIR2.Eval.Result.AllocationLaws.of_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Result.AllocationLaws.of_accounting

/-- info: 'Compilatrix.IxIR2.Eval.Result.AllocationLaws.reclaimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Result.AllocationLaws.reclaimed

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithAllocationEvents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithAllocationEvents

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithAllocationEvents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithAllocationEvents

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.baselineNoReuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.baselineNoReuses

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainAllocationLaws

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalAllocationLaws

/-- info: 'Compilatrix.Recursion.Lowered.physicalMainAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Lowered.physicalMainAllocationLaws

/-- info: 'Compilatrix.Recursion.Compilation.sourceRefinesSelectedWithAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Compilation.sourceRefinesSelectedWithAllocationLaws

/-! Comparative RC and peak-live bounds, including every selected prefix and
complete shared reclamation. The existing axiom basis is unchanged. -/

/-- info: 'Compilatrix.IxIR2.Eval.releaseSharedWork_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.releaseSharedWork_observations

/-- info: 'Compilatrix.IxIR2.Eval.InstructionTransferCase.rcCharge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.InstructionTransferCase.rcCharge

/-- info: 'Compilatrix.IxIR2.Eval.Step.peakRecords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Step.peakRecords

/-- info: 'Compilatrix.IxIR2.Eval.runMachine_prefix_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.runMachine_prefix_costs

/-- info: 'Compilatrix.IxIR2.ReuseSim.StableHeapRel.pendingRC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseSim.StableHeapRel.pendingRC_eq

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.unchangedStep_costDelta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.unchangedStep_costDelta

/-- info: 'Compilatrix.IxIR2.Eval.CostDelta.hot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CostDelta.hot

/-- info: 'Compilatrix.IxIR2.Eval.CostDelta.cold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.CostDelta.cold

/-- info: 'Compilatrix.IxIR2.Eval.Result.CostBounds.reclaimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Result.CostBounds.reclaimed

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithCosts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithCosts

/-- info: 'Compilatrix.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithCosts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithCosts

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostBounds

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPrefixCostBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPrefixCostBounds

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainCostLaws

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostLaws

/-- info: 'Compilatrix.Recursion.Lowered.physicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Lowered.physicalMainCostLaws

/-- info: 'Compilatrix.Recursion.Compilation.sourceRefinesSelectedWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Compilation.sourceRefinesSelectedWithCostLaws

/-! R5: direct-call credit suspension, reservation ownership, actual selected
compiler execution, and closed source-map specialization. -/

/-- info: 'Compilatrix.IxIR2.Eval.Policy.runMain_v0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.runMain_v0

/-- info: 'Compilatrix.IxIR2.Eval.Policy.suspendCall_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.suspendCall_iff

/-- info: 'Compilatrix.IxIR2.Eval.Policy.Step.reservationOwnership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.Step.reservationOwnership

/-- info: 'Compilatrix.IxIR2.Eval.Policy.Steps.reservationOwnership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.Steps.reservationOwnership

/-- info: 'Compilatrix.IxIR2.Eval.Policy.runMain_prefix_reservationOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.runMain_prefix_reservationOwnership

/-- info: 'Compilatrix.IxIR2.Eval.Policy.runMain_allocationAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.runMain_allocationAccounting

/-- info: 'Compilatrix.IxIR2.Eval.Policy.runMachine_prefix_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.runMachine_prefix_costs

/-- info: 'Compilatrix.IxIR2.Eval.Policy.runMain_success_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Policy.runMain_success_unique

/-- info: 'Compilatrix.IxIR2.CallReuse.Selection.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CallReuse.Selection.valid

/-- info: 'Compilatrix.IxIR2.CallReuse.Sim.simulate_to_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CallReuse.Sim.simulate_to_halt

/-- info: 'Compilatrix.IxIR2.CallReuse.Output.mainSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CallReuse.Output.mainSimulation

/-- info: 'Compilatrix.IxIR2.CallReuse.Selection.mainSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CallReuse.Selection.mainSimulation

/-- info: 'Compilatrix.Pipeline.LoweredCompilation.owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.LoweredCompilation.owned

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.baselineClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.baselineClosed

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedCallPrefixCostBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedCallPrefixCostBounds

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedCallPhysicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.selectedCallPhysicalMainCostLaws

/-- info: 'Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulCallPhysicalCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.CompiledAttachment.successfulCallPhysicalCostLaws

/-- info: 'Compilatrix.CallReuse.Compilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.CallReuse.Compilation.sourceRefinesWithCostLaws

/-- info: 'Compilatrix.IxIR0.MapRecovery.sourceMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MapRecovery.sourceMap

/-- info: 'Compilatrix.IxIR0.MapRecovery.targetMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MapRecovery.targetMap

/-- info: 'Compilatrix.IxIR0.MapRecovery.Recovered.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MapRecovery.Recovered.forwardSimulation

/-- info: 'Compilatrix.IxIR0.MapRecovery.Selection.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MapRecovery.Selection.forwardSimulation

/-- info: 'Compilatrix.IxIR0.MapRecovery.Recovered.projectionSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MapRecovery.Recovered.projectionSafe

/-- info: 'Compilatrix.CallReuse.MapLowered.physicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.CallReuse.MapLowered.physicalMainCostLaws

/-- info: 'Compilatrix.CallReuse.MapCompilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.CallReuse.MapCompilation.sourceRefinesWithCostLaws

/-! Static unique source reversal: saturated source modes, consuming emission,
actual SSA execution, every physical prefix, exact costs, and full release. -/

/-- info: 'Compilatrix.Pipeline.CertifiedErasure.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.CertifiedErasure.sourceRefines

/-- info: 'Compilatrix.IxIR0.RecursorInstance.address_eq_iff_bytes_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.RecursorInstance.address_eq_iff_bytes_eq

/-- info: 'Compilatrix.IxIR0.UniqueReverse.Checked.sourceEvaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.UniqueReverse.Checked.sourceEvaluates

/-- info: 'Compilatrix.IxIR0.UniqueReverse.Recovered.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.UniqueReverse.Recovered.forwardSimulation

/-- info: 'Compilatrix.UniqueReuse.CheckedSource.sourceValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.CheckedSource.sourceValue

/-- info: 'Compilatrix.UniqueReuse.ListAt.hasWorld' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.ListAt.hasWorld

/-- info: 'Compilatrix.UniqueReuse.ListAt.graph' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.ListAt.graph

/-- info: 'Compilatrix.UniqueReuse.consumingLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.consumingLoop

/-- info: 'Compilatrix.UniqueReuse.mainExists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.mainExists

/-- info: 'Compilatrix.UniqueReuse.consumingMainResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.consumingMainResult

/-- info: 'Compilatrix.UniqueReuse.release1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.release1

/-- info: 'Compilatrix.UniqueReuse.release2_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.release2_complete

/-- info: 'Compilatrix.UniqueReuse.Target.reserveReuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.reserveReuse

/-- info: 'Compilatrix.UniqueReuse.Target.reuseAt_peak' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.reuseAt_peak

/-- info: 'Compilatrix.UniqueReuse.Target.loopSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.loopSteps

/-- info: 'Compilatrix.UniqueReuse.Target.mainSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.mainSteps

/-- info: 'Compilatrix.UniqueReuse.Target.mainRuns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.mainRuns

/-- info: 'Compilatrix.UniqueReuse.Target.MainResult.reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.MainResult.reclaims

/-- info: 'Compilatrix.UniqueReuse.Target.prefixResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.prefixResources

/-- info: 'Compilatrix.UniqueReuse.Target.costLaws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Target.costLaws

/-- info: 'Compilatrix.IxIR2.UniqueLower.Translation.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.UniqueLower.Translation.forwardSimulation

/-- info: 'Compilatrix.UniqueReuse.ownedSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.ownedSemantics

/-- info: 'Compilatrix.UniqueReuse.backendSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.backendSemantics

/-- info: 'Compilatrix.UniqueReuse.Compilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Compilation.sourceRefinesWithCostLaws

/-! Bounded native unique reversal: byte-memory realization, full emitted
entry and release runs, and unchanged source-contract/axiom boundaries. -/

/-- info: 'Compilatrix.X86.Memory.read64_write64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Memory.read64_write64

/-- info: 'Compilatrix.X86.UniqueExecution.mainAndRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueExecution.mainAndRelease

/-- info: 'Compilatrix.X86.UniqueExecution.NativeList.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueExecution.NativeList.nodup

/-- info: 'Compilatrix.UniqueReuse.Native.Output.executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Output.executes

/-- info: 'Compilatrix.UniqueReuse.Native.Output.costsAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Output.costsAgree

/-- info: 'Compilatrix.UniqueReuse.Native.Output.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Output.sourceRefines

/-- info: 'Compilatrix.UniqueReuse.Native.SourceNativeResult.witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.SourceNativeResult.witness

/-- info: 'Compilatrix.UniqueReuse.Native.Execution.mainSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Execution.mainSafe

/-- info: 'Compilatrix.UniqueReuse.Native.Execution.releaseSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Native.Execution.releaseSafe

/-! General logical/physical credit refinement, both policies and the whole
instruction language. These bridges add no native hashing or new axioms. -/

/-- info: 'Compilatrix.IxIR2.CreditRefinement.step_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.step_related

/-- info: 'Compilatrix.IxIR2.CreditRefinement.prefix_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.prefix_resources

/-- info: 'Compilatrix.IxIR2.CreditRefinement.runMain_prefix_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.runMain_prefix_resources

/-- info: 'Compilatrix.IxIR2.CreditRefinement.checked_runMain_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.checked_runMain_refines

/-- info: 'Compilatrix.IxIR2.CreditRefinement.runMain_v0_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.runMain_v0_refines

/-- info: 'Compilatrix.IxIR2.CreditRefinement.runMain_refines_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.runMain_refines_independent

/-- info: 'Compilatrix.IxIR2.CreditRefinement.OutcomeRel.ownership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.OutcomeRel.ownership

/-- info: 'Compilatrix.IxIR2.CreditRefinement.OutcomeRel.valueGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.OutcomeRel.valueGraph

/-- info: 'Compilatrix.IxIR2.CreditRefinement.OutcomeRel.reclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.OutcomeRel.reclamation

/-- info: 'Compilatrix.IxIR2.CreditRefinement.checked_runMain_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.CreditRefinement.checked_runMain_owned

/-! Runtime source application and a single native reversal function. The
native input, validation, execution, and rejection proofs add no semantic
axiom; addressed compiler certificates retain the existing hash axiom. -/

/-- info: 'Compilatrix.Sim.apply_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.apply_sim_inlineSharing

/-- info: 'Compilatrix.UniqueReuse.Runtime.Compilation.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Compilation.sourceRefines

/-- info: 'Compilatrix.UniqueReuse.Runtime.Compilation.targetRuns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Compilation.targetRuns

/-- info: 'Compilatrix.UniqueReuse.Runtime.Target.makeInput_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Target.makeInput_valid

/-- info: 'Compilatrix.X86.RuntimeExecution.validationSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.validationSteps

/-- info: 'Compilatrix.X86.RuntimeExecution.executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.executes

/-- info: 'Compilatrix.X86.RuntimeExecution.canonical_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.canonical_executes

/-- info: 'Compilatrix.X86.RuntimeExecution.Execution.mainSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.Execution.mainSafe

/-- info: 'Compilatrix.X86.RuntimeExecution.Execution.releaseSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.Execution.releaseSafe

/-- info: 'Compilatrix.X86.RuntimeExecution.lengthRejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.lengthRejects

/-- info: 'Compilatrix.X86.RuntimeExecution.capacityRejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.capacityRejects

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.ArgumentRel.graph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.ArgumentRel.graph

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefines

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.costsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.costsAgree

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.ofNats_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.ofNats_exact

/-- info: 'Compilatrix.X86.RuntimeExecution.inputWordsStep_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeExecution.inputWordsStep_eq

/-! Adjacent reserve/reuse counter folding preserves final general-purpose
registers, arena words, and the source-to-object contract without a new semantic axiom. -/

/-- info: 'Compilatrix.X86.UniqueCounterFold.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueCounterFold.state_eq

/-- info: 'Compilatrix.X86.UniqueCounterFold.trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueCounterFold.trace

/-- info: 'Compilatrix.X86.UniqueCounterFold.instruction_saving' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.X86.UniqueCounterFold.instruction_saving

/-- info: 'Compilatrix.X86.RuntimeTarget.controlCost_saving' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.RuntimeTarget.controlCost_saving

/-! Borrowed ABI checking, finite closed-program execution certificates,
source agreement, actual RC/peak laws, and checked baseline fallback. -/

/-- info: 'Compilatrix.IxIR2.Borrow.Checked.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Checked.valid

/-- info: 'Compilatrix.IxIR2.Borrow.Checked.exactRewrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Checked.exactRewrite

/-- info: 'Compilatrix.IxIR2.Borrow.Execution.steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Execution.steps

/-- info: 'Compilatrix.IxIR2.Borrow.Improved.preservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Improved.preservation

/-- info: 'Compilatrix.IxIR2.Borrow.Improved.resources' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Improved.resources

/-- info: 'Compilatrix.IxIR2.Borrow.Selection.fallbackExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Selection.fallbackExact

/-- info: 'Compilatrix.Borrow.Improved.sourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Improved.sourcePreservation

/-- info: 'Compilatrix.Borrow.Improved.resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Improved.resources

/-- info: 'Compilatrix.Borrow.Selection.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Selection.valid

/-- info: 'Compilatrix.Borrow.Selection.fallbackExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Selection.fallbackExact

/-! Open borrowed functions: structurally derived calls and continuations,
exact lender-store preservation, arbitrary owned input reclamation, and
the actual source-to-runtime composition. No input replay selects a variant. -/

/-- info: 'Compilatrix.IxIR2.Borrow.Open.retain_release_cancel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Open.retain_release_cancel

/-- info: 'Compilatrix.IxIR2.Borrow.Open.Entry.steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Open.Entry.steps

/-- info: 'Compilatrix.IxIR2.Borrow.Open.Entry.lenderLifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Open.Entry.lenderLifetime

/-- info: 'Compilatrix.IxIR2.Borrow.Open.Entry.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Open.Entry.total

/-- info: 'Compilatrix.IxIR2.Borrow.Open.Certificate.strictImprovement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Open.Certificate.strictImprovement

/-- info: 'Compilatrix.IxIR2.Borrow.Open.Certificate.controlCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Open.Certificate.controlCost

/-- info: 'Compilatrix.IxIR2.Borrow.Open.Certificate.runFunctions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Borrow.Open.Certificate.runFunctions

/-- info: 'Compilatrix.Borrow.Runtime.Source.Shape.applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Source.Shape.applies

/-- info: 'Compilatrix.Borrow.Runtime.Tree.counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Tree.counts

/-- info: 'Compilatrix.Borrow.Runtime.Argument.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Argument.input

/-- info: 'Compilatrix.Borrow.Runtime.Certified.sourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Certified.sourcePreservation

/-- info: 'Compilatrix.Borrow.Runtime.Certified.runtimePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Certified.runtimePreservation

/-- info: 'Compilatrix.Borrow.Runtime.Certified.sourceToRuntime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Certified.sourceToRuntime

/-- info: 'Compilatrix.Borrow.Runtime.Selection.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Selection.valid

/-- info: 'Compilatrix.Borrow.Runtime.Selection.fallbackExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Borrow.Runtime.Selection.fallbackExact

/-! E1 consumes actual emitted bytes through an independent parser. All local
encoding, flag, memory-fault and control laws use only the ordinary logical
axioms; whole-stream layout and reference ISA agreement remain separate. -/

/-- info: 'Compilatrix.X86.Encode.instruction_decodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.instruction_decodeAt

/-- info: 'Compilatrix.X86.Encode.terminator_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.terminator_decode

/-- info: 'Compilatrix.X86.Encode.encoded_instruction_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.encoded_instruction_execution

/-- info: 'Compilatrix.X86.Encode.compare_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.compare_execution

/-- info: 'Compilatrix.X86.Encode.branch_bytes_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.branch_bytes_execution

/-- info: 'Compilatrix.X86.Encode.branch_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.branch_patch

/-- info: 'Compilatrix.X86.Encode.call_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.call_pair

/-- info: 'Compilatrix.X86.Encode.call_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.call_fault

/-- info: 'Compilatrix.X86.Encode.ret_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.ret_pair

/-- info: 'Compilatrix.X86.Encode.relative_resolves_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.relative_resolves_base

/-- info: 'Compilatrix.X86.Encode.patchSigned32_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.patchSigned32_splice

/-- info: 'Compilatrix.X86.Encode.signed32_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Encode.signed32_checked

/-! E2 composes complete streams, explicit call-slot memory correspondence,
independent ELF interpretation, PC32 relocation and the emitted N2 source
endpoint. Only indexed source claims retain the existing native hash axiom. -/

/-- info: 'Compilatrix.X86.Stream.pcOffset_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.pcOffset_injective

/-- info: 'Compilatrix.X86.Stream.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.check_sound

/-- info: 'Compilatrix.X86.Stream.linear_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.linear_step

/-- info: 'Compilatrix.X86.Stream.branch_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.branch_at

/-- info: 'Compilatrix.X86.Stream.call_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.call_progress

/-- info: 'Compilatrix.X86.Stream.ret_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.ret_progress

/-- info: 'Compilatrix.X86.Stream.run_to_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.run_to_return

/-- info: 'Compilatrix.X86.Stream.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.run_with_calls

/-- info: 'Compilatrix.X86.Stream.run_permissions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.Stream.run_permissions

/-- info: 'Compilatrix.X86.StreamExamples.reused_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.StreamExamples.reused_safe

/-- info: 'Compilatrix.X86.StreamExamples.nested_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.StreamExamples.nested_safe

/-- info: 'Compilatrix.X86.ELF.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELF.check_sound

/-- info: 'Compilatrix.X86.ELF.Valid.text' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.X86.ELF.Valid.text

/-- info: 'Compilatrix.X86.ELF.Valid.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELF.Valid.entry

/-- info: 'Compilatrix.X86.ELFLink.pc32_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELFLink.pc32_call

/-- info: 'Compilatrix.X86.ELFLink.Applied.resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELFLink.Applied.resolves

/-- info: 'Compilatrix.X86.ELFLink.runtime_call_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ELFLink.runtime_call_transfer

/-- info: 'Compilatrix.X86.ObjectEval.run_from_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.run_from_typed

/-- info: 'Compilatrix.X86.ObjectEval.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.ObjectEval.run_with_calls

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Output.emit_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Output.emit_spec

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.role_callFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.role_callFree

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Object.provenance_parsed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Object.provenance_parsed

/-- info: 'Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects

/-! C3 reuses only equal erased preimages. Closed Nat translation validation
and explicit execution certificates compose with the original source bridge. -/

/-- info: 'Compilatrix.IxIR0.Readdress.blockMembers_eq_of_compatibleBlocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.blockMembers_eq_of_compatibleBlocks

/-- info: 'Compilatrix.IxIR0.Readdress.members_eq_of_compatibleBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.members_eq_of_compatibleBlocks

/-- info: 'Compilatrix.IxIR2.Pipeline.Attached.sourcePhysical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Pipeline.Attached.sourcePhysical

/-- info: 'Compilatrix.X86.NatCalls.Output.refinesSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.Output.refinesSuccessfulRun

/-- info: 'Compilatrix.X86.NatCalls.Execution.objectReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.Execution.objectReturns

/-- info: 'Compilatrix.X86.NatCalls.sourceObjectRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.X86.NatCalls.sourceObjectRefines
