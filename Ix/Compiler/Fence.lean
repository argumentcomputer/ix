import Ix.Compiler.Sim
import Ix.Compiler.X86.NatCallsSim
import Ix.Compiler.X86.ScalarSourceObject
import Ix.Compiler.X86.PhysicalScalarSourceObject
import Ix.Compiler.X86.PhysicalScalarCapturedSourceObject
import Ix.Compiler.UniqueReuse.PipelineSim
import Ix.Compiler.UniqueReuse.NativeSim
import Ix.Compiler.UniqueReuse.RuntimeNativeSim
import Ix.Compiler.UniqueReuse.RuntimeObjectSim
import Ix.Compiler.X86.RuntimeReject
import Ix.Compiler.X86.ByteBranch
import Ix.Compiler.X86.ByteCall
import Ix.Compiler.X86.StreamExamples
import Ix.Compiler.IxIR2.CreditRefinement
import Ix.Compiler.Borrow.Pipeline
import Ix.Compiler.Borrow.RuntimeSim
import Ix.Compiler.Borrow.RuntimeInput
import Ix.Compiler.IxIR1.Sim
import Ix.Compiler.IxIR1.Reclamation
import Ix.Compiler.IxIR1.LowerSim
import Ix.Compiler.IxIR1.LowerProgress
import Ix.Compiler.IxIR1.LowerAddressedSim
import Ix.Compiler.IxIR1.LowerFullyAddressedSim
import Ix.Compiler.IxIR1.NoReuseAddressed
import Ix.Compiler.IxIR1.CostInstance
import Ix.Compiler.IxIR1.CostModel
import Ix.Compiler.IxIR1.CostTrace
import Ix.Compiler.IxIR1.LowerMutualAddressedSim
import Ix.Compiler.IxIR1.LowerMutualAddressedProgress
import Ix.Compiler.IxIR0.Decode
import Ix.Compiler.IxIR0.MutualBlock
import Ix.Compiler.IxIR0.ReaddressSim
import Ix.Compiler.IxIR0.ProjectionFree
import Ix.Compiler.IxIR0.DynamicCost
import Ix.Compiler.IxIR0.ReaddressProjectionSafe
import Ix.Compiler.IxIR0.ReaddressOracle
import Ix.Compiler.IxIR0.ReaddressOracleExamples
import Ix.Compiler.EraseAddressedSim
import Ix.Compiler.IxIR1.Decode
import Ix.Compiler.IxIR1.MutualBlock
import Ix.Compiler.IxIR1.ReaddressAll
import Ix.Compiler.IxIR1.HPT
import Ix.Compiler.IxIR1.HPTSound
import Ix.Compiler.IxIR1.HPTProduce
import Ix.Compiler.IxIR1.HPTCache
import Ix.Compiler.IxIR1.HPTCasePrune
import Ix.Compiler.IxIR1.HPTCasePruneProgram
import Ix.Compiler.IxIR1.HPTPAPFuse
import Ix.Compiler.IxIR1.HPTFetchForward
import Ix.Compiler.IxIR1.HPTDestroy
import Ix.Compiler.IxIR1.Reachability
import Ix.Compiler.IxIR1.HPTPAPFuseProgram
import Ix.Compiler.SimInstance
import Ix.Compiler.UsageSound
import Ix.Compiler.Ixon.Address
import Ix.Compiler.Ixon.Const
import Ix.Compiler.IxIR2.EvalCounter
import Ix.Compiler.IxIR2.Lower
import Ix.Compiler.IxIR2.LowerSim
import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.IxIR2.PipelineSim
import Ix.Compiler.IxIR2.LivenessExamples
import Ix.Compiler.IxIR2.Reuse
import Ix.Compiler.IxIR2.ReuseSim
import Ix.Compiler.IxIR2.ReuseLiveSim
import Ix.Compiler.IxIR2.ReuseSimExamples
import Ix.Compiler.IxIR2.ReuseExamples
import Ix.Compiler.X86.Basic
import Ix.Compiler.X86.Eval
import Ix.Compiler.X86.EvalExamples
import Ix.Compiler.X86.Select
import Ix.Compiler.X86.PipelineSim
import Ix.Compiler.X86.SelectExamples
import Ix.Compiler.X86.Encode
import Ix.Compiler.X86.EncodeExamples
import Ix.Compiler.X86.ELF
import Ix.Compiler.X86.ELFExamples
import Ix.Compiler.Pipeline
import Ix.Compiler.PipelineSound
import Ix.Compiler.Recursion.Sim
import Ix.Compiler.Recursion.PhysicalSim
import Ix.Compiler.Recursion.Resources
import Ix.Compiler.Recursion.Allocation
import Ix.Compiler.Recursion.Costs
import Ix.Compiler.CallReuse.Sim
import Ix.Compiler.CallReuse.MapSim

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

/-! ## Erasure simulation (`Ix/Compiler/Sim.lean`) -/

/-- info: 'Ix.Compiler.Ixon.Eval.projectValue_ok_of_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Eval.projectValue_ok_of_strict

/-- info: 'Ix.Compiler.Sim.erasure_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_sim

/-- info: 'Ix.Compiler.Sim.erasure_sim_with_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_sim_with_members

/-- info: 'Ix.Compiler.Sim.erasure_sim_projectionSafe_with_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_sim_projectionSafe_with_members

/-- info: 'Ix.Compiler.Sim.erasure_sim_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_sim_closed

/-- info: 'Ix.Compiler.Sim.erasure_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_sim_inlineSharing

/-- info: 'Ix.Compiler.Sim.erasure_sim_inlineSharing_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_sim_inlineSharing_closed

/-- info: 'Ix.Compiler.Sim.erasure_proj_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_proj_sim

/-- info: 'Ix.Compiler.Sim.erasure_proj_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.erasure_proj_sim_inlineSharing

/-- info: 'Ix.Compiler.SimInstance.ghostDefinitionHeadSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.ghostDefinitionHeadSim

/-- info: 'Ix.Compiler.SimInstance.quotientIndSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.quotientIndSim

/-- info: 'Ix.Compiler.SimInstance.externAnswerSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.externAnswerSim

/-- info: 'Ix.Compiler.SimInstance.pairSplitProjectionSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.pairSplitProjectionSim

/-- info: 'Ix.Compiler.SimInstance.indexedRecSplitSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.indexedRecSplitSim

/-- info: 'Ix.Compiler.SimInstance.indexedRecSelfSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.indexedRecSelfSim

/-- info: 'Ix.Compiler.SimInstance.definitionProjectionSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.definitionProjectionSim

/-- info: 'Ix.Compiler.SimInstance.mutualInductiveMemberSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.mutualInductiveMemberSim

/-- info: 'Ix.Compiler.SimInstance.cyclicDefinitionMembersSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.cyclicDefinitionMembersSim

/-- info: 'Ix.Compiler.SimInstance.cyclicRecursorMembersSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.cyclicRecursorMembersSim

/-- info: 'Ix.Compiler.SimInstance.opaqueMutualMemberSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.opaqueMutualMemberSim

/-- info: 'Ix.Compiler.SimInstance.opaqueMutualProjectionSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.opaqueMutualProjectionSim

/-! ## Usage-checker non-interference (`Ix/Compiler/UsageSound.lean`)

Pin the generic common-erasure observation theorem, its contentful checked
and certified dropped-variable instance, and the corresponding whole-entry
forward simulation. -/

/-- info: 'Ix.Compiler.Ixon.UsageCheck.closureWorld_shared_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.UsageCheck.closureWorld_shared_iff

/-- info: 'Ix.Compiler.Ixon.UsageCheck.check_lam_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.UsageCheck.check_lam_shared

/-- info: 'Ix.Compiler.UsageSound.computedErased_eval_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UsageSound.computedErased_eval_noninterference

/-- info: 'Ix.Compiler.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceNoninterference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceNoninterference

/-- info: 'Ix.Compiler.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceSim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UsageSound.DroppedVariableFixture.droppedVariableOccurrenceSim

/-! ## IxIR₀ → IxIR₁ lowering soundness (`Ix/Compiler/IxIR1/Sim.lean`) -/

/-- info: 'Ix.Compiler.IxIR1.Sim.reuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.reuse_sound

/-- info: 'Ix.Compiler.IxIR1.Sim.reuse_shared_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.reuse_shared_sound

/-- info: 'Ix.Compiler.IxIR1.Sim.invoke_fn_result_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.invoke_fn_result_hasWorld

/-! ## IxIR₁ reclamation (`Ix/Compiler/IxIR1/Reclamation.lean`,
`Ix/Compiler/IxIR1/NoReuse.lean`, and
`Ix/Compiler/IxIR1/NoReuseAddressed.lean`)

Pin the finite empty-root theorem, the public semantic bridge, the actual
no-`reuse` compiler proof, and its pure address-transport boundary.  The
production SCC corollary additionally carries the already-ledgered native
BLAKE3 audit axiom. -/

/-- info: 'Ix.Compiler.IxIR1.Reclamation.live_eq_zero_of_empty_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reclamation.live_eq_zero_of_empty_roots

/-- info: 'Ix.Compiler.IxIR1.Reclamation.shared_reclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reclamation.shared_reclamation

/-- info: 'Ix.Compiler.IxIR1.LowerSim.reclamation_of_run_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.reclamation_of_run_invariants

/-- info: 'Ix.Compiler.IxIR1.LowerSim.reclamation_of_run_ownership_and_zero_reuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.reclamation_of_run_ownership_and_zero_reuses

/-- info: 'Ix.Compiler.IxIR1.Reclamation.runMain_order_of_reuses_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reclamation.runMain_order_of_reuses_eq_zero

/-- info: 'Ix.Compiler.IxIR1.Reclamation.runOp_order_of_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reclamation.runOp_order_of_reuses_eq

/-- info: 'Ix.Compiler.IxIR1.NoReuse.runMain_reuses_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.runMain_reuses_eq_zero

/-- info: 'Ix.Compiler.IxIR1.NoReuse.runOp_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.runOp_reuses_eq

/-- info: 'Ix.Compiler.IxIR1.NoReuse.invoke_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.invoke_reuses_eq

/-- info: 'Ix.Compiler.IxIR1.NoReuse.applyGo_reuses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.applyGo_reuses_eq

/-- info: 'Ix.Compiler.IxIR1.Sim.runOwnedMain_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.runOwnedMain_ok

/-- info: 'Ix.Compiler.IxIR1.NoReuse.checkCode_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.checkCode_eq_true_iff

/-- info: 'Ix.Compiler.IxIR1.NoReuse.checkDeclarations_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.checkDeclarations_eq_true_iff

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_main_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_main_owned

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllAction_noReuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllAction_noReuse

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllAction_reclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllAction_reclamation

/-- info: 'Ix.Compiler.IxIR1.NoReuse.reclamation_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.reclamation_mapAddresses

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_raw

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw

/-! ## IxIR₁ cost refinement (`Ix/Compiler/IxIR1/LowerSim.lean`,
`Ix/Compiler/IxIR1/NoReuse.lean`, and
`Ix/Compiler/IxIR1/NoReuseAddressed.lean`, and
`Ix/Compiler/IxIR1/CostInstance.lean`, and
`Ix/Compiler/IxIR1/CostModel.lean`,
`Ix/Compiler/IxIR0/DynamicCost.lean`,
`Ix/Compiler/IxIR0/ProjectionFree.lean`, and
`Ix/Compiler/IxIR1/CostTrace.lean`)

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

/-- info: 'Ix.Compiler.IxIR1.Reclamation.runMain_nodes_size_eq_allocs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reclamation.runMain_nodes_size_eq_allocs

/-- info: 'Ix.Compiler.IxIR1.Reclamation.runMain_live_add_frees_eq_allocs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reclamation.runMain_live_add_frees_eq_allocs

/-- info: 'Ix.Compiler.IxIR1.LowerSim.RunCostInvariant.costRefinement' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.RunCostInvariant.costRefinement

/-- info: 'Ix.Compiler.IxIR1.LowerSim.CostRefinement.and' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.CostRefinement.and

/-- info: 'Ix.Compiler.IxIR1.LowerSim.allocationFreeCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.allocationFreeCostRefinement

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllAction_reuseCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllAction_reuseCostRefinement

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllAction_costRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllAction_costRefinement

/-- info: 'Ix.Compiler.IxIR1.NoReuse.runCostInvariant_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.runCostInvariant_mapAddresses

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_runCostInvariant_of_exact_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_runCostInvariant_of_exact_raw

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reuseCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_reuseCostRefinement

/-- info: 'Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_costRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.NoReuse.lowerAllIndexedFullyAddressed_costRefinement

/-- info: 'Ix.Compiler.IxIR1.CostInstance.exactCostRefinement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostInstance.exactCostRefinement

/-- info: 'Ix.Compiler.IxIR1.CostInstance.loweringCostWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostInstance.loweringCostWitness

/-- info: 'Ix.Compiler.IxIR1.CostModel.lowerAllAction_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostModel.lowerAllAction_run

/-- info: 'Ix.Compiler.IxIR1.CostModel.sourceSensitiveCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostModel.sourceSensitiveCostRefinement

/-- info: 'Ix.Compiler.IxIR1.CostModel.sourceSensitiveBoundsCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostModel.sourceSensitiveBoundsCostRefinement

/-- info: 'Ix.Compiler.IxIR1.CostModel.loweringCostWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostModel.loweringCostWitness

/-- info: 'Ix.Compiler.IxIR0.DynamicCost.Eval.ofTrace' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.DynamicCost.Eval.ofTrace

/-- info: 'Ix.Compiler.IxIR0.DynamicCost.Applies.append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.DynamicCost.Applies.append

/-- info: 'Ix.Compiler.IxIR0.ProjectionFree.Eval.of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.ProjectionFree.Eval.of_run

/-- info: 'Ix.Compiler.IxIR1.CostTrace.ProfileCostRefinement.of_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.ProfileCostRefinement.of_witness

/-- info: 'Ix.Compiler.IxIR0.DynamicCost.Eval.surfaceEvals_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.DynamicCost.Eval.surfaceEvals_le

/-- info: 'Ix.Compiler.IxIR1.CostTrace.ObservationGrowthLE.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.ObservationGrowthLE.trans

/-- info: 'Ix.Compiler.IxIR1.CostTrace.dupVals_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.dupVals_growth

/-- info: 'Ix.Compiler.IxIR1.CostTrace.withinBudget_ownershipAmortized_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.withinBudget_ownershipAmortized_iff

/-- info: 'Ix.Compiler.IxIR1.CostTrace.RcPotentialGrowthLE.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.RcPotentialGrowthLE.trans

/-- info: 'Ix.Compiler.IxIR1.CostTrace.dupVals_rcPotential_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.dupVals_rcPotential_growth

/-- info: 'Ix.Compiler.IxIR1.CostTrace.dropVal_amortizedRc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.dropVal_amortizedRc

/-- info: 'Ix.Compiler.IxIR1.CostTrace.dropUVal_amortizedRc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.dropUVal_amortizedRc

/-- info: 'Ix.Compiler.IxIR1.CostTrace.runOp_localRcPotential_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.runOp_localRcPotential_growth

/-- info: 'Ix.Compiler.IxIR1.CostTrace.OpRcPotentialSound.of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.OpRcPotentialSound.of_local

/-- info: 'Ix.Compiler.IxIR1.CostTrace.EmitRcPotentialSound.comp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.EmitRcPotentialSound.comp

/-- info: 'Ix.Compiler.IxIR1.CostTrace.EmitRcPotentialSound.localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.EmitRcPotentialSound.localOp

/-- info: 'Ix.Compiler.IxIR1.CostTrace.dropVal_allocs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.dropVal_allocs

/-- info: 'Ix.Compiler.IxIR1.CostTrace.runOp_localOwnership_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.runOp_localOwnership_growth

/-- info: 'Ix.Compiler.IxIR1.CostTrace.OpOwnershipCostSound.of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.OpOwnershipCostSound.of_local

/-- info: 'Ix.Compiler.IxIR1.CostTrace.EmitOwnershipCostSound.comp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.EmitOwnershipCostSound.comp

/-- info: 'Ix.Compiler.IxIR1.CostTrace.EmitOwnershipCostSound.localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.EmitOwnershipCostSound.localOp

/-- info: 'Ix.Compiler.IxIR1.CostTrace.ProfileFundedEmitStateRunSound.ofOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.ProfileFundedEmitStateRunSound.ofOp

/-- info: 'Ix.Compiler.IxIR1.CostTrace.ProfileFundedApplyRun.papOver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.ProfileFundedApplyRun.papOver

/-- info: 'Ix.Compiler.IxIR1.CostTrace.LowerResultProfileSound.installThen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.LowerResultProfileSound.installThen

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerE_let_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerE_let_run_profile_sound

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerBorrow_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerBorrow_run_profile_sound

/-- info: 'Ix.Compiler.IxIR1.CostTrace.projectionSlotReleased_profileFundedEmitStateRunSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.projectionSlotReleased_profileFundedEmitStateRunSound

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerE_proj_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerE_proj_run_profile_sound

/-- info: 'Ix.Compiler.IxIR1.LowerSim.papp_graph_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.papp_graph_op

/-- info: 'Ix.Compiler.IxIR1.CostTrace.LowerResultProfileSound.consArgs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.LowerResultProfileSound.consArgs

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerCaptures_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerCaptures_run_profile_sound

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerLam_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerLam_run_profile_sound

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerE_lam_run_profile_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerE_lam_run_profile_sound

/-- info: 'Ix.Compiler.IxIR1.CostTrace.sourceProfileOwnershipAllowance_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.sourceProfileOwnershipAllowance_add

/-- info: 'Ix.Compiler.IxIR1.CostTrace.CodeOwnershipCostSound.runCertificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.CodeOwnershipCostSound.runCertificate

/-- info: 'Ix.Compiler.IxIR1.CostTrace.CodeOwnershipCostSound.withinBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.CodeOwnershipCostSound.withinBudget

/-- info: 'Ix.Compiler.IxIR1.CostTrace.OwnershipAmortizedRunCertificate.spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.OwnershipAmortizedRunCertificate.spec

/-- info: 'Ix.Compiler.IxIR1.CostTrace.ProfileCostRefinement.of_ownershipAmortizedCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.ProfileCostRefinement.of_ownershipAmortizedCertificate

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerAllAction_compilerProfileContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerAllAction_compilerProfileContracts

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerAllAction_main_ownershipAmortizedCertificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerAllAction_main_ownershipAmortizedCertificate_sealed

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerAllAction_profileCostRefinement_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerAllAction_profileCostRefinement_sealed

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_sealed

/-- info: 'Ix.Compiler.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_exact_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.CostTrace.lowerAllIndexedFullyAddressed_profileCostRefinement_exact_sealed

/-! ## Whole-pass lowering instance (`Ix/Compiler/SimInstance.lean`)

The four boundaries the M2b ledger claims for the actual compiled
`add 2̂ 3̂` output: exact ownership contracts, the source-to-target
`ValueGraph` forward simulation, all-fuel memory-error exclusion, and the
call/recursion-sensitive source-profile cost refinement.
Pinning them here is what makes
"without `native_decide`" mechanical rather than editorial. -/

/-- info: 'Ix.Compiler.SimInstance.addIxIR1CompilerContracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.addIxIR1CompilerContracts

/-- info: 'Ix.Compiler.SimInstance.addIxIR1SemanticForwardSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.addIxIR1SemanticForwardSimulation

/-- info: 'Ix.Compiler.SimInstance.addIxIR1MemoryErrorUnreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.addIxIR1MemoryErrorUnreachable

/-- info: 'Ix.Compiler.SimInstance.addIxIR1DynamicCostRefinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.SimInstance.addIxIR1DynamicCostRefinement

/-! ## Generic whole-pass target safety
(`Ix/Compiler/IxIR1/LowerProgress.lean`) -/

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_memoryErrorUnreachable_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_memoryErrorUnreachable_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_unknownRefUnreachable_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_unknownRefUnreachable_sealed

/-! ## Content-addressed lowering transport
(`Ix/Compiler/IxIR1/ReaddressSim.lean`,
`Ix/Compiler/IxIR1/ReaddressOwnership.lean`,
`Ix/Compiler/IxIR1/LowerAddressedSim.lean`)

The generic evaluator proof is independent of hashing.  The production
corollaries consume a successful native BLAKE3 post-pass run, so the exact
native implementation axiom is an intentional, mechanically visible member
of those cones.  Pin the indexed artifact boundary used by `Pipeline` across
identity protection, exact runs, addressed value graphs, all three dynamic
error classes, and cost counters. -/

/-- info: 'Ix.Compiler.IxIR1.Readdress.evalTransportAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Readdress.evalTransportAt

/-- info: 'Ix.Compiler.IxIR1.Readdress.applyGo_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Readdress.applyGo_mapAddresses

/-- info: 'Ix.Compiler.IxIR1.Readdress.dupVals_success_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Readdress.dupVals_success_preimage

/-- info: 'Ix.Compiler.IxIR1.Readdress.dropVal_success_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Readdress.dropVal_success_preimage

/-- info: 'Ix.Compiler.IxIR1.Readdress.runOp_success_preimage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Readdress.runOp_success_preimage

/-- info: 'Ix.Compiler.IxIR1.Sim.rootOwnership_mapAddresses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.rootOwnership_mapAddresses_iff

/-- info: 'Ix.Compiler.IxIR1.Readdress.runMain_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Readdress.runMain_mapAddresses

/-! IxIR₀ now has the corresponding full-value transport: closures,
constructor identities, PAP heads, oracle calls, and address-bearing errors
all commute with the map. -/

/-- info: 'Ix.Compiler.IxIR0.Readdress.evalTransportAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.evalTransportAt

/-- info: 'Ix.Compiler.IxIR0.Readdress.Ctx.run_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.Ctx.run_mapAddresses

/-- info: 'Ix.Compiler.IxIR0.Readdress.ProjectionSafe.Eval.mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.ProjectionSafe.Eval.mapAddresses

/-! The executable oracle view reverse-resolves only declaration keys and
maps returned values forward. Its compatibility theorem remains independent
of hashing; the successful production wrapper below exposes the native hash
boundary used to construct the recorded program map. -/

/-- info: 'Ix.Compiler.IxIR0.Readdress.Oracle.readdress_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.Oracle.readdress_compatible

/-- info: 'Ix.Compiler.EraseAddressed.run_readdressOracle_semantics_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.EraseAddressed.run_readdressOracle_semantics_of_run_eq_ok

/-! The cycle-safe IxIR₀ block codec is pure, while successful transient-name
materialization intentionally crosses the same native BLAKE3 boundary. -/

/-- info: 'Ix.Compiler.IxIR0.MutualBlock.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MutualBlock.semanticAudit_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.MutualBlock.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.MutualBlock.semanticAudit_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.ReaddressAll.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ReaddressAll.semanticAudit_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.ReaddressAll.reserved_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ReaddressAll.reserved_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.ReaddressAll.rebuildSemanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ReaddressAll.rebuildSemanticAudit_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.ReaddressAll.Result.raw_lookup_of_mem_of_rebuildSemanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ReaddressAll.Result.raw_lookup_of_mem_of_rebuildSemanticAudit

/-- info: 'Ix.Compiler.IxIR1.ReaddressAll.Result.declaration_preimage_of_lookup_of_rebuildSemanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ReaddressAll.Result.declaration_preimage_of_lookup_of_rebuildSemanticAudit

/-! Checked HPT summaries expose both the untrusted candidate's post-fixpoint
condition and the exact cache/content-address audit. Materialization uses the
same ledgered BLAKE3 boundary as the program artifacts. -/

/-- info: 'Ix.Compiler.IxIR1.HPT.postFixpoint_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.postFixpoint_of_runWith_eq_ok

/-- info: 'Ix.Compiler.IxIR1.HPT.semanticAudit_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.semanticAudit_of_runWith_eq_ok

/-- info: 'Ix.Compiler.IxIR1.HPT.postFixpoint_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.postFixpoint_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.HPT.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.semanticAudit_of_run_eq_ok

/-! The abstract interpreter's evaluator concretization is pure.  Composing
that theorem with accepted native-addressed certificates exposes exactly the
same ledgered BLAKE3 axiom as the existing post-fixpoint/materialization
boundary, including through the pipeline API. -/

/-! Recursive field refinement itself is hash-independent. These pins cover
the mutually recursive order transport and both directions of the bounded
root/field conversion used by allocation, fetch, and case binders. -/

/-- info: 'Ix.Compiler.IxIR1.HPT.FieldShape.holds_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FieldShape.holds_of_le

/-- info: 'Ix.Compiler.IxIR1.HPT.FieldFact.holds_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FieldFact.holds_of_le

/-- info: 'Ix.Compiler.IxIR1.HPT.FieldFactsHold.holds_of_listLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FieldFactsHold.holds_of_listLe

/-- info: 'Ix.Compiler.IxIR1.HPT.HeapShape.toFieldShape_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.HeapShape.toFieldShape_holds

/-- info: 'Ix.Compiler.IxIR1.HPT.FieldShape.toHeapShape_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FieldShape.toHeapShape_holds

/-- info: 'Ix.Compiler.IxIR1.HPT.FieldFact.ofFact_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FieldFact.ofFact_holds

/-- info: 'Ix.Compiler.IxIR1.HPT.FieldFact.toFact_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FieldFact.toFact_holds

/-- info: 'Ix.Compiler.IxIR1.HPT.Fact.exactConstructor?_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Fact.exactConstructor?_eq_some

/-- info: 'Ix.Compiler.IxIR1.HPT.Fact.exactConstructor?_holds_loc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Fact.exactConstructor?_holds_loc

/-- info: 'Ix.Compiler.IxIR1.HPT.Fact.caseFields_ctor_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Fact.caseFields_ctor_holds

/-- info: 'Ix.Compiler.IxIR1.HPT.Fact.caseFields_natSucc_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Fact.caseFields_natSucc_holds

/-- info: 'Ix.Compiler.IxIR1.HPT.analyzeOp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.analyzeOp_sound

/-- info: 'Ix.Compiler.IxIR1.HPT.invoke_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.invoke_sound

/-- info: 'Ix.Compiler.IxIR1.HPT.functionSummary_sound_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.functionSummary_sound_of_runWith_eq_ok

/-- info: 'Ix.Compiler.IxIR1.HPT.functionSummary_sound_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.functionSummary_sound_of_run_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_checkHPTWith_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_checkHPT_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_checkHPT_eq_ok

/-! Deterministic production remains outside the trust boundary: its output
stores an equality showing that the ordinary checker accepted it.  These pins
make the resulting post-fixpoint, audit, and evaluator guarantees expose the
same native materialization dependency and nothing further. -/

/-- info: 'Ix.Compiler.IxIR1.HPT.Production.postFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Production.postFixpoint

/-- info: 'Ix.Compiler.IxIR1.HPT.Production.semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Production.semanticAudit

/-- info: 'Ix.Compiler.IxIR1.HPT.Production.functionSummary_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Production.functionSummary_sound

/-- info: 'Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_producedHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_producedHPT

/-! Persistent-cache hits and artifact-local rebuilds are likewise outside the
trust boundary: the returned value stores the exact ordinary checker equality.
The filesystem adapter carries no theorem and cannot weaken these cones. -/

/-- info: 'Ix.Compiler.IxIR1.HPT.Cache.Production.postFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Cache.Production.postFixpoint

/-- info: 'Ix.Compiler.IxIR1.HPT.Cache.Production.semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Cache.Production.semanticAudit

/-- info: 'Ix.Compiler.IxIR1.HPT.Cache.Production.functionSummary_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Cache.Production.functionSummary_sound

/-- info: 'Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_cachedHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.functionSummary_sound_of_cachedHPT

/-! The first HPT consumer, including owner-sensitive whole-function fact
propagation, recursive supplied-code traversal, self-call-aware rewriting, and
declaration-graph rebuilding, is pure through its logical old-keyed layer.
Checked, directly produced, cached, and content-address rebuild wrappers add
exactly the already-ledgered native digest dependency, and no
transformation-specific assumption. -/

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runCode_runWithFacts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runCode_runWithFacts_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runCode_rewriteCurrentAt_body_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runCode_rewriteCurrentAt_body_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runCode_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runCode_run_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runCode_run_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runCode_run_eq_of_runWith_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.runCode_pruneCase_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runCode_pruneCase_of_checkHPTWith_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.runCode_pruneCaseWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runCode_pruneCaseWithProducedHPT_eq

/-- info: 'Ix.Compiler.Pipeline.Artifact.runCode_pruneCaseWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runCode_pruneCaseWithCachedHPT_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runCode_runRecursive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runCode_runRecursive_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_runWith_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.runCode_pruneCasesRecursive_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runCode_pruneCasesRecursive_of_checkHPTWith_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.runCode_pruneCasesRecursiveWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runCode_pruneCasesRecursiveWithProducedHPT_eq

/-- info: 'Ix.Compiler.Pipeline.Artifact.runCode_pruneCasesRecursiveWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runCode_pruneCasesRecursiveWithCachedHPT_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runMain_runRecursive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runMain_runRecursive_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_runWith_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.runMain_pruneMain_of_checkHPTWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runMain_pruneMain_of_checkHPTWith_eq_ok

/-- info: 'Ix.Compiler.Pipeline.Artifact.runMain_pruneMainWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runMain_pruneMainWithProducedHPT_eq

/-- info: 'Ix.Compiler.Pipeline.Artifact.runMain_pruneMainWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runMain_pruneMainWithCachedHPT_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runMain_rewriteProgram_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runMain_rewriteProgram_eq

/-- info: 'Ix.Compiler.IxIR1.ReaddressAll.runMain_exact_of_rebuild_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ReaddressAll.runMain_exact_of_rebuild_eq_ok

/-- info: 'Ix.Compiler.IxIR1.ReaddressAll.runMain_exact_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ReaddressAll.runMain_exact_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram

/-! Scalar fetch forwarding is exact both at one accepted constructor/fetch
pair and through its owner-sensitive recursive traversal. -/

/-- info: 'Ix.Compiler.IxIR1.HPT.FetchForward.runCode_forwardHead?_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FetchForward.runCode_forwardHead?_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.FetchForward.runCode_runWithFacts_eq_ownerCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.FetchForward.runCode_runWithFacts_eq_ownerCompatible

/-! Shape-specialized destruction is pure at both the accepted local
decision and the complete owner-sensitive fact traversal. -/

/-- info: 'Ix.Compiler.IxIR1.HPT.Destroy.runOp_specialize?_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Destroy.runOp_specialize?_success

/-- info: 'Ix.Compiler.IxIR1.HPT.Destroy.runCode_runWithFacts_success_ownerCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.Destroy.runCode_runWithFacts_success_ownerCompatible

/-! Rooted reachability is exact after validation and through its fail-soft
produce/check/apply wrapper.  Both public theorems expose the native BLAKE3
axiom because validation commits to the exact input graph digest. -/

/-- info: 'Ix.Compiler.IxIR1.Reachability.runMain_filterEntries_eq_of_validate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reachability.runMain_filterEntries_eq_of_validate

/-- info: 'Ix.Compiler.IxIR1.Reachability.runMain_run_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Reachability.runMain_run_eq

/-! The first allocation-shrinking consumer is pure through both the generic
heap-history evaluator congruence and its executable local decision theorem. -/

/-- info: 'Ix.Compiler.IxIR1.Sim.HeapHistoryIso.toHeapIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.HeapHistoryIso.toHeapIso

/-- info: 'Ix.Compiler.IxIR1.Sim.HeapHistoryIso.toHeapIso_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.HeapHistoryIso.toHeapIso_rel

/-- info: 'Ix.Compiler.IxIR1.Sim.HeapHistoryIso.of_toHeapIso_rel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.HeapHistoryIso.of_toHeapIso_rel

/-- info: 'Ix.Compiler.IxIR1.Sim.runCode_historyIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.runCode_historyIso

/-- info: 'Ix.Compiler.IxIR1.HPT.PAPFuse.fusePair?_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.PAPFuse.fusePair?_refines

/-- info: 'Ix.Compiler.IxIR1.Sim.runCode_abstractEnvironment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.runCode_abstractEnvironment

/-- info: 'Ix.Compiler.IxIR1.Sim.runCode_exactEnvironment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.runCode_exactEnvironment_eq

/-- info: 'Ix.Compiler.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle

/-! Fail-soft optimizer reclamation uses one forwarded execution, evaluator
determinism, allocation-history release transport, and the exact final rebuild.
The produced and cached wrappers expose the same native digest boundary as the
checked HPT and rebuild inputs. -/

/-- info: 'Ix.Compiler.IxIR1.Optimizer.Outcome.reclamation_of_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Optimizer.Outcome.reclamation_of_witness

/-- info: 'Ix.Compiler.IxIR1.Optimizer.reclamation_of_runWithProducedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Optimizer.reclamation_of_runWithProducedHPT_eq

/-- info: 'Ix.Compiler.IxIR1.Optimizer.reclamation_of_runWithCachedHPT_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Optimizer.reclamation_of_runWithCachedHPT_eq

/-- info: 'Ix.Compiler.Pipeline.Artifact.runMain_pruneProgram_of_checkAndPruneProgramWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.Artifact.runMain_pruneProgram_of_checkAndPruneProgramWith_eq_ok

/-- info: 'Ix.Compiler.IxIR0.Readdress.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.semanticAudit_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR0.Readdress.Result.declaration_lookup_of_mem_of_semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.Result.declaration_lookup_of_mem_of_semanticAudit

/-- info: 'Ix.Compiler.IxIR0.Readdress.isolates_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.isolates_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR0.Readdress.Oracle.Readdressable.examples_of_isolates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.Oracle.Readdressable.examples_of_isolates

/-- info: 'Ix.Compiler.IxIR0.Readdress.Oracle.Readdressable.examples_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.Oracle.Readdressable.examples_of_run_eq_ok

/-- info: 'Ix.Compiler.EraseAddressed.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.EraseAddressed.semanticAudit_of_run_eq_ok

/-- info: 'Ix.Compiler.EraseAddressed.run_semantics_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.EraseAddressed.run_semantics_of_run_eq_ok

/-- info: 'Ix.Compiler.EraseAddressed.run_projectionSafeMain_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.EraseAddressed.run_projectionSafeMain_of_run_eq_ok

/-- info: 'Ix.Compiler.IxIR1.LowerSim.AddressedSemanticForwardSimulation.precomposeIxIR0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.AddressedSemanticForwardSimulation.precomposeIxIR0

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_after_addressedErasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_after_addressedErasure

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_protectsSourceAddresses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_protectsSourceAddresses

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_memoryErrorUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_memoryErrorUnreachable

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_ordinaryStuckUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_ordinaryStuckUnreachable

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_unknownRefUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_unknownRefUnreachable

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_runMain_cost

/-! The SCC-aware production boundary carries the same native digest axiom
and now permits source-function rekeying while auditing constructor stability. -/

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_exact_success

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_apply_constructorIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_apply_constructorIdentity

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_exact

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_memoryErrorUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_memoryErrorUnreachable

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_ordinaryStuckUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_ordinaryStuckUnreachable

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_unknownRefUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_unknownRefUnreachable

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_runMain_cost

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_after_addressedErasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_after_addressedErasure

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_exact_after_addressedErasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_exact_after_addressedErasure

/-! ## Erasure-safe whole-pass progress
(`Ix/Compiler/IxIR1/LowerProgress.lean`)

The certified-erasure route rules out the raw lowering's erased-projection
absorber.  Pin both the source-side projection-safety bridge and the resulting
whole-main progress/simulation boundaries.  The call-aware pins additionally
ensure that callable target progress is reconstructed from exact source-fuel
traces and whole-pass provenance, rather than from `CompilerProgressContracts`.
-/

/-- info: 'Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_erasure

/-- info: 'Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_with_members

/-- info: 'Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_inlineSharing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_erasure_inlineSharing

/-- info: 'Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_certifiedSharedClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.ProjectionSafeEval.of_certifiedSharedClosed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_inlineSharing_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_inlineSharing_with_members

/-- info: 'Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_with_members

/-- info: 'Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_erasure_with_members

/-- info: 'Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.CallAwareProjectionSafe.of_certifiedSharedClosed_addressed_with_members

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_main_progress_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_main_progress_of_certificate_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAddressed_semanticForwardSimulation_of_certificate_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_certificate_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedAction_main_progress_of_addressed_certificate_with_members_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_addressed_certificate_with_members_exact_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_main_progress_of_addressed_certificate_with_members_exact_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_exact_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_exact_sealed

/-! The validated pipeline retains the exact member scope, erasure certificate,
member coverage, and both address-pass equations consumed by the production
semantic endpoint.  Its O1 projection pins semantic preservation, progress,
memory-error exclusion, reclamation, and the evaluator-universal allocation/
free law directly on the artifact selected by the fail-soft optimizer. -/

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.targetDeclEnv_ne_extern' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.targetDeclEnv_ne_extern

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.externValueContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.externValueContract

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.externTraceProgressContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.externTraceProgressContract

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.semanticForwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.semanticForwardSimulation

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.semanticForwardSimulationOfProducedOptimizedArtifact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.semanticForwardSimulationOfProducedOptimizedArtifact

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.targetProgressAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.targetProgressAfterProducedOptimization

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.memoryErrorUnreachableAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.memoryErrorUnreachableAfterProducedOptimization

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.reclamationAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.reclamationAfterProducedOptimization

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.allocationFreeCostInvariantAfterProducedOptimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.allocationFreeCostInvariantAfterProducedOptimization

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.sourceCallableRowsSelected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.sourceCallableRowsSelected

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.sourceDeclLayout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.sourceDeclLayout

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.sourcePapSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.sourcePapSafe

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.fnDeclCovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.fnDeclCovered

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.exactExtraRepresented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.exactExtraRepresented

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.exactCompilerContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.exactCompilerContracts

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.targetProgress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.targetProgress

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.memoryErrorUnreachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.memoryErrorUnreachable

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.reclamation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.reclamation

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.costRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.costRefinement

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.ownershipAmortizedCostRefinement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.ownershipAmortizedCostRefinement

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_compilerTraceProgressContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_compilerTraceProgressContracts

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_main_progress_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_main_progress_of_certificate_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_main_progress_of_projectionSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_main_progress_of_projectionSafe

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_ordinaryStuckUnreachable_of_erasure_inlineSharing_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_ordinaryStuckUnreachable_of_erasure_inlineSharing_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_erasure_inlineSharing_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_erasure_inlineSharing_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_sealed

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_trace_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_semanticForwardSimulation_of_certificate_trace_sealed

/-! ## Owner-sensitive dynamic application

Dynamic PAP entry is guarded by declaration metadata, while saturated direct
calls retain heterogeneous ownership boundaries. These pins keep the computed
metadata, whole-pass provenance, strictly-weaker mixed-mode premise, and joint
contract seal inside the ordinary proof axiom envelope. -/

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_sourceDeclLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_sourceDeclLayout

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_sourcePapSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_sourcePapSafe

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_fnDeclCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_fnDeclCovered

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_extraProvenance_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_extraProvenance_empty

/-- info: 'Ix.Compiler.IxIR1.LowerSim.GeneratedDeclProvenance.fnPreservesAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.GeneratedDeclProvenance.fnPreservesAt

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_sourceFnPreservesAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_sourceFnPreservesAt

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_compilerContracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_compilerContracts

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerDecl_defn_papSafe_of_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerDecl_defn_papSafe_of_run

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerDecl_recursor_papSafe_of_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerDecl_recursor_papSafe_of_run

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerAllAction_compilerFunction_declPapSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerAllAction_compilerFunction_declPapSafe

/-- info: 'Ix.Compiler.IxIR1.LowerSim.SourceAllShared.papSafe' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.SourceAllShared.papSafe

/-- info: 'Ix.Compiler.IxIR1.LowerSim.sourcePapSafe_not_sourceAllShared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.sourcePapSafe_not_sourceAllShared

/-- info: 'Ix.Compiler.IxIR1.LowerSim.papSafeDeclContractsBelow_of_source_extra' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.papSafeDeclContractsBelow_of_source_extra

/-- info: 'Ix.Compiler.IxIR1.LowerSim.compilerContracts_of_source_extra_below_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.compilerContracts_of_source_extra_below_step

/-- info: 'Ix.Compiler.IxIR1.Sim.applyOwnershipContract_of_papSafeDecls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.applyOwnershipContract_of_papSafeDecls

/-! ## Semantic projection (`Ix/Compiler/IxIR1/LowerSim.lean`)

The premise-free member of the projection value pipeline: variable-target
projection needs no compiler-induction hypothesis, so its cone is the whole
borrow/fetch/retain/release argument. -/

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerE_proj_var_run_value_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerE_proj_var_run_value_sound

/-- info: 'Ix.Compiler.IxIR1.LowerSim.lowerE_proj_erasure_run_value_progress_within' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.LowerSim.lowerE_proj_erasure_run_value_progress_within

/-! ## Indexed address environments (`Ix/Compiler/AddressEnv.lean`)

The corpus path builds each hash index once, while these equalities retain the
transparent first-binding-wins list semantics as the proof specification. -/

/-- info: 'Ix.Compiler.AddressEnv.lookup_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.AddressEnv.lookup_build

/-- info: 'Ix.Compiler.IxIR1.Lower.lowerAllIndexed_eq_lowerAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Lower.lowerAllIndexed_eq_lowerAll

/-- info: 'Ix.Compiler.Pipeline.ResolverIndex.resolve_ofList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ResolverIndex.resolve_ofList

/-! ## Codec laws -/

/-- info: 'Ix.Compiler.Ixon.Address.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Address.roundtripLaw

/-- info: 'Ix.Compiler.Ixon.Address.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Address.canonicalLaw

/-- info: 'Ix.Compiler.Ixon.Univ.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Univ.roundtripLaw

/-- info: 'Ix.Compiler.Ixon.Univ.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Univ.canonicalLaw

/-- info: 'Ix.Compiler.Ixon.Expr.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Expr.roundtripLaw

/-- info: 'Ix.Compiler.Ixon.Expr.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Expr.canonicalLaw

/-- info: 'Ix.Compiler.Ixon.ConstantInfo.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.ConstantInfo.roundtripLaw

/-- info: 'Ix.Compiler.Ixon.ConstantInfo.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.ConstantInfo.canonicalLaw

/-- info: 'Ix.Compiler.Ixon.Constant.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Constant.roundtripLaw

/-- info: 'Ix.Compiler.Ixon.Constant.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Ixon.Constant.canonicalLaw

/-- info: 'Ix.Compiler.IxIR0.Decl.decodePreimage_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Decl.decodePreimage_roundtrip

/-- info: 'Ix.Compiler.IxIR0.Decl.decodePreimage_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Decl.decodePreimage_canonical

/-- info: 'Ix.Compiler.IxIR0.Decl.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Decl.preimage_injective

/-- info: 'Ix.Compiler.IxIR1.Decl.decodePreimage_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Decl.decodePreimage_roundtrip

/-- info: 'Ix.Compiler.IxIR1.Decl.decodePreimage_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Decl.decodePreimage_canonical

/-- info: 'Ix.Compiler.IxIR1.Decl.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Decl.preimage_injective

/-- info: 'Ix.Compiler.IxIR0.MutualBlock.Block.decodePreimage_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MutualBlock.Block.decodePreimage_roundtrip

/-- info: 'Ix.Compiler.IxIR0.MutualBlock.Block.decodePreimage_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MutualBlock.Block.decodePreimage_canonical

/-- info: 'Ix.Compiler.IxIR0.MutualBlock.Block.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MutualBlock.Block.preimage_injective

/-- info: 'Ix.Compiler.IxIR1.MutualBlock.Block.decodePreimage_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.MutualBlock.Block.decodePreimage_roundtrip

/-- info: 'Ix.Compiler.IxIR1.MutualBlock.Block.decodePreimage_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.MutualBlock.Block.decodePreimage_canonical

/-- info: 'Ix.Compiler.IxIR1.MutualBlock.Block.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.MutualBlock.Block.preimage_injective

/-! ## IxIR₂ credit-counter algebra -/

/-- info: 'Ix.Compiler.IxIR2.Eval.CounterLaw.afterHotReset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CounterLaw.afterHotReset

/-- info: 'Ix.Compiler.IxIR2.Eval.CounterLaw.afterReuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CounterLaw.afterReuse

/-- info: 'Ix.Compiler.IxIR2.Eval.CounterLaw.afterDiscard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CounterLaw.afterDiscard

/-- info: 'Ix.Compiler.IxIR2.Eval.CounterLaw.terminalFrees' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CounterLaw.terminalFrees

/-! ## IxIR₂ structured-lowering acceptance -/

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.headBlock_mem_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.headBlock_mem_blocks

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.blocks_subset_of_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.blocks_subset_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.blocks_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.blocks_subset

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountMatches' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountMatches

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountsMatch' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountMatches_of_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountMatches_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCount_eq_headParams_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCount_eq_headParams_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountsMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.entryValueCountsMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.entryValueCountsMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.entryValueCountsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.inductTree' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.inductTree

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.letOpSyntax_of_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.letOpSyntax_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.operationSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.operationSyntax_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.letOpOperationSyntax_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.letOpOperationSyntax_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.retSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.retSyntax_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.tailCallSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.tailCallSyntax_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.tailCallSelfSyntax_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.tailCallSelfSyntax_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.switchSyntax_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.switchSyntax_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.syntaxMatches_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.syntaxMatches_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.syntaxMatches' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.syntaxMatches

/-- info: 'Ix.Compiler.IxIR2.Lower.fetchPrologueAt_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.fetchPrologueAt_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_getElem?

/-- info: 'Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_tag

/-- info: 'Ix.Compiler.IxIR2.Lower.constructorBranchMatchAt_of_switch_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.constructorBranchMatchAt_of_switch_match

/-- info: 'Ix.Compiler.IxIR2.Lower.natZeroBranchMatchAt_of_switch_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.natZeroBranchMatchAt_of_switch_match

/-- info: 'Ix.Compiler.IxIR2.Lower.natBranchPairMatch_of_switch_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.natBranchPairMatch_of_switch_match

/-- info: 'Ix.Compiler.IxIR2.Lower.switchBranchShape_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.switchBranchShape_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.switchBranchesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.switchBranchesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantSwitchBranchesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantSwitchBranchesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.letOpMatch_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.letOpMatch_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.instructionAt_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.instructionAt_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.headBlock_eq_sourceBlock_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.headBlock_eq_sourceBlock_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.InputMap.forgets_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.InputMap.forgets_of_check

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.inputMapForgets_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.inputMapForgets_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.inputMapSize_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.inputMapSize_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.instructionsMatch_of_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.instructionsMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.instructionsMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.instructionsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.inputMapsMatch_of_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.inputMapsMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.inputMapsMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.inputMapsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.functionSourceMatch_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.functionSourceMatch_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.functionSourceEq_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.functionSourceEq_eq_true_iff

/-- info: 'Ix.Compiler.IxIR2.Lower.inputEq_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.inputEq_eq_true_iff

/-- info: 'Ix.Compiler.IxIR2.Lower.functionTraceMatch_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.functionTraceMatch_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.rootSourceCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.rootSourceCode

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.sourceArity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.sourceArity

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.sourceResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.sourceResult

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.sourcePapSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.sourcePapSafe

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.entryBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.entryBlock

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.entryPc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.entryPc

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.entryValueCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.entryValueCount

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.entryInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.entryInput

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.rootHeadBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.rootHeadBlock

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainOwner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainOwner

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainSource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainSource

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainGenerated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainGenerated

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainArity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainArity

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainRootSourceCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainRootSourceCode

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainEntryInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainEntryInput

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainHeadBlockAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainHeadBlockAt

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainNonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainNonempty

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.blockAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.blockAt

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.blockAt_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.blockAt_of_mem

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.headBlockAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.headBlockAt

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantHeadBlockAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantHeadBlockAt

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantInstructionsMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantInstructionsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantInputMapsMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantInputMapsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantEntryValueCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantEntryValueCount

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantSyntaxMatches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantSyntaxMatches

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantOperationSyntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantOperationSyntax

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.generatedNonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.generatedNonempty

/-- info: 'Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantLetOpMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.FunctionTrace.descendantLetOpMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.programTraceOrder_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.programTraceOrder_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.functionTrace_of_source_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.functionTrace_of_source_mem

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.valid

/-- info: 'Ix.Compiler.IxIR2.Lower.CheckedRun.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CheckedRun.valid

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.resolveAtom_of_envRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.resolveAtom_of_envRel

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.resolveAtom_of_envRel_target' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.resolveAtom_of_envRel_target

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.initial' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.initial

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.empty

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.blockAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.blockAt

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.instructionAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.instructionAt

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.letOpNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.letOpNext

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.forget' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.forget

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.forgetTracedValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.forgetTracedValue

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.forgetTracedErased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.forgetTracedErased

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.entry

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.functionEntryCodeState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.functionEntryCodeState

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.initialMainState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.initialMainState

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.initialMainCodeState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.initialMainCodeState

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.runMain_eq_initialMainMachine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.runMain_eq_initialMainMachine

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.resolveAtom_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.resolveAtom_shift

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.sourceMapOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.sourceMapOf

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.constructorFields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.constructorFields

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_edge_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_edge_transfer

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.resolvedAtoms_of_resolveAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.resolvedAtoms_of_resolveAtoms

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.resolveAtoms_exists_of_pointwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.resolveAtoms_exists_of_pointwise

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.ResolvedAtomsList.getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.ResolvedAtomsList.getElem?

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.of_edge_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.of_edge_arguments

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_edge_transfer_from_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_edge_transfer_from_parent

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EdgeArgsRel.canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EdgeArgsRel.canonical

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_generated_edge_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_generated_edge_transfer

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.edgeRuntimeReady_of_envRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.edgeRuntimeReady_of_envRel

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.move' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.move

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.resolveAtoms_of_envRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.resolveAtoms_of_envRel

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.resolveAtoms_of_envRel_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.resolveAtoms_of_envRel_target

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.atomsRel_of_translateAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.atomsRel_of_translateAtoms

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.bindValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.bindValue

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.letOpValueNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.letOpValueNext

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_pure_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_pure_move

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_pure_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_pure_move

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_pure_move_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_pure_move_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_pure_move_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_pure_move_success_step

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.alloc

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.alloc' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.alloc

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_alloc

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_alloc_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_alloc_state

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.pappFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.pappFn

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_papp_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_papp_fn

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_papp_fn_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_papp_fn_state

/-- info: 'Ix.Compiler.IxIR2.Eval.RetainSharedMany.empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.RetainSharedMany.empty

/-- info: 'Ix.Compiler.IxIR2.Eval.RetainSharedMany.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.RetainSharedMany.cons

/-- info: 'Ix.Compiler.IxIR2.Eval.RetainSharedMany.cons_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.RetainSharedMany.cons_inv

/-- info: 'Ix.Compiler.IxIR2.Eval.ApplyTransfer.erased' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ApplyTransfer.erased

/-- info: 'Ix.Compiler.IxIR2.Eval.ApplyTransfer.papUnder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ApplyTransfer.papUnder

/-- info: 'Ix.Compiler.IxIR2.Eval.ApplyTransfer.papFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ApplyTransfer.papFn

/-- info: 'Ix.Compiler.IxIR2.Eval.ApplyTransfer.papExtern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ApplyTransfer.papExtern

/-- info: 'Ix.Compiler.IxIR2.Eval.ApplyTransferCase.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ApplyTransferCase.transfer

/-- info: 'Ix.Compiler.IxIR2.Eval.ApplyTransfer.classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ApplyTransfer.classify

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.apply

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.retApplyMore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.retApplyMore

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dupVals_simulates_retainSharedMany' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dupVals_simulates_retainSharedMany

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.empty

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.positiveSharedRC' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.positiveSharedRC

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtom

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtoms

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtomsReverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.resolveAtomsReverse

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.constructorBranch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.constructorBranch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.natSuccessor' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.natSuccessor

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCode

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOp

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.invoke

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGo

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCodeNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runCodeNoReuse

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOpNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.runOpNoReuse

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.invokeNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.invokeNoReuse

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGoNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceRuntimeInvariant.applyGoNoReuse

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.PositiveSharedRC.dupVals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.PositiveSharedRC.dupVals

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_prepare

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_erased

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_pap_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_pap_under

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_pap_saturated_enter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_pap_saturated_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_pap_over_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_applyGo_pap_over_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_under

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_saturated_enter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_saturated_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_over_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_apply_pap_over_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_apply_transfer_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_apply_transfer_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_apply_pap_saturated_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_apply_pap_saturated_enter_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_apply_pap_over_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_apply_pap_over_enter_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_apply_more' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_apply_more

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_apply_more_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_apply_more_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.source_runOp_call_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.source_runOp_call_eq

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.source_runOp_callSelf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.source_runOp_callSelf_eq

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.source_runCode_tail_call_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.source_runCode_tail_call_eq

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.source_runCode_tail_callSelf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.source_runCode_tail_callSelf_eq

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_call_fn_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_call_fn_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_call_self_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_call_self_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_tail_call_fn_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_tail_call_fn_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_tail_call_self_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_tail_call_self_enter

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_call_fn_enter_source_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_call_self_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_call_self_enter_source_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_tail_call_fn_enter_source_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_tail_call_self_enter_source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_tail_call_self_enter_source_state

/-- info: 'Ix.Compiler.IxIR2.Eval.Steps.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Steps.trans

/-- info: 'Ix.Compiler.IxIR2.Eval.initialMachine_store_empty' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.initialMachine_store_empty

/-- info: 'Ix.Compiler.IxIR2.Eval.runFunction_eq_runMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runFunction_eq_runMachine

/-- info: 'Ix.Compiler.IxIR2.Eval.runMain_eq_runMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runMain_eq_runMachine

/-- info: 'Ix.Compiler.IxIR2.Eval.Steps.runMachine' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Steps.runMachine

/-- info: 'Ix.Compiler.IxIR2.Eval.Steps.runMachine_halted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Steps.runMachine_halted

/-! The credit-aware evaluator proof seam used by reuse-insertion proofs. -/

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditLookup.of_getElem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditLookup.of_getElem

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditTake.of_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditTake.of_lookup

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditTakeMany.single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditTakeMany.single

/-- info: 'Ix.Compiler.IxIR2.Eval.ConstructorView.of_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ConstructorView.of_box

/-- info: 'Ix.Compiler.IxIR2.Eval.ConstructorView.parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ConstructorView.parts

/-- info: 'Ix.Compiler.IxIR2.Eval.EdgeTransfer.of_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.EdgeTransfer.of_parts

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.branchCreditPresent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.branchCreditPresent

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.branchCreditAbsent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.branchCreditAbsent

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.allocWithAbsent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.allocWithAbsent

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.allocWithLogical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.allocWithLogical

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.allocWithPhysical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.allocWithPhysical

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.discardCreditAbsent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.discardCreditAbsent

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.discardCreditLogical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.discardCreditLogical

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.discardCreditPhysical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.discardCreditPhysical

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.takeUniqueLogical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.takeUniqueLogical

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.takeUniquePhysical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.takeUniquePhysical

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.resetSharedLogicalHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.resetSharedLogicalHot

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.resetSharedPhysicalHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.resetSharedPhysicalHot

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.resetSharedCold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.resetSharedCold

/-- info: 'Ix.Compiler.IxIR2.Eval.EdgeTransfer.baseline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.EdgeTransfer.baseline

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.jump

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.switchCtor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.switchCtor

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.switchNatZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.switchNatZero

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.switchNatSucc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.switchNatSucc

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.callFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.callFn

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.callSelf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.callSelf

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.tailCallFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.tailCallFn

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.tailCallSelf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.tailCallSelf

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.tailCallSelfCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.tailCallSelfCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.retResumeCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.retResumeCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.retHaltCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.retHaltCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.retApplyMoreCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.retApplyMoreCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.tailCallFnCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.tailCallFnCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.callFnCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.callFnCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.callSelfCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.callSelfCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.pappFnCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.pappFnCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.pappExternCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.pappExternCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.externCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.externCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.applyCleared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.applyCleared

/-- info: 'Ix.Compiler.IxIR2.Eval.InstructionTransferCase.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.InstructionTransferCase.step

/-- info: 'Ix.Compiler.IxIR2.Eval.InstructionTransfer.classify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.InstructionTransfer.classify

/-- info: 'Ix.Compiler.IxIR2.Eval.TerminatorTransferCase.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.TerminatorTransferCase.step

/-- info: 'Ix.Compiler.IxIR2.Eval.TerminatorTransfer.classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.TerminatorTransfer.classify

/-- info: 'Ix.Compiler.IxIR2.Eval.StepCase.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.StepCase.step

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.classify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.classify

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.retResume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.retResume

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_letOp_continuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_letOp_continuation

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_case_ctor_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_case_ctor_branch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_case_nat_zero_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_case_nat_zero_branch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_case_nat_succ_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_case_nat_succ_branch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_fetch_prologue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_fetch_prologue

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_switch_ctor_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_switch_ctor_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_switch_nat_zero_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_switch_nat_zero_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_switch_nat_succ_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_switch_nat_succ_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_resume

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_resume_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_resume_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_return_to_letOp_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_return_to_letOp_state

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.retHalt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.retHalt

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_halt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_halt

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_halt_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_halt_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_halt_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_ret_halt_success

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_halt_runMachine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_ret_halt_runMachine

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.retainShared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.retainShared

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.rcTick' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.rcTick

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_dup_retain_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_dup_retain_scalar

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_dup_retain_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_dup_retain_shared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.fetch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_fetch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_fetch_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_fetch_state

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.releaseShared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.releaseShared

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.freeUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.freeUnique

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.kill' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.kill

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.releaseShared_of_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.releaseShared_of_scalar

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.EnvRel.bindErased' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.EnvRel.bindErased

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_scalar

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_free_freeUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_free_freeUnique

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_free_freeUnique_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_free_freeUnique_state

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.dropUnique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.dropUnique

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropUnique_of_scalar' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropUnique_of_scalar

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_shared_nonunit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_shared_nonunit

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.sourceDropMany_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.sourceDropMany_of_scalars

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.sourceDropManyU_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.sourceDropManyU_of_scalars

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_of_scalars

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropUniqueWork_of_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropUniqueWork_of_scalars

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar_ctor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_dropU_dropUnique_scalar_ctor

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_shared_unit_scalar_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_shared_unit_scalar_ctor

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropUniqueWork_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropUniqueWork_append

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.uniqueDropWork_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.uniqueDropWork_simulation

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropUVal_simulates_dropUniqueWork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropUVal_simulates_dropUniqueWork

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropManyU_simulates_dropUniqueWork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropManyU_simulates_dropUniqueWork

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_dropU_dropUnique_recursive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_dropU_dropUnique_recursive

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_dropU_dropUnique_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_dropU_dropUnique_recursive_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_append

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_success_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_success_unique

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.sharedReleaseWork_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.sharedReleaseWork_simulation

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropVal_simulates_releaseSharedWork' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropVal_simulates_releaseSharedWork

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropMany_simulates_releaseSharedWork' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropMany_simulates_releaseSharedWork

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_recursive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_drop_release_recursive

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_drop_release_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_drop_release_recursive_state

/-- info: 'Ix.Compiler.IxIR2.Eval.FieldWorlds.of_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.FieldWorlds.of_replicate

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.hasWorld_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.hasWorld_eq_true_iff

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate_of_ownership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_replicate_of_ownership

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.resultWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.CodeStateRel.resultWorld

/-- info: 'Ix.Compiler.IxIR2.Lower.ProgramTraceOrder.main_of_mem_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.ProgramTraceOrder.main_of_mem_owner

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.functionTraceSource_eq_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.functionTraceSource_eq_of_match

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_of_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_descendant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.codeScalarLeavesMatch_descendant

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.functionCodeScalarLeavesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.functionCodeScalarLeavesMatch

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_of_codeScalarLeavesMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_of_codeScalarLeavesMatch

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_of_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_descendant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.codeExactFetchesMatch_descendant

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.functionCodeExactFetchesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.functionCodeExactFetchesMatch

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_of_codeExactFetchesMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_of_codeExactFetchesMatch

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.mainAnalysisCurrentCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.mainAnalysisCurrentCompatible

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.functionTraceAnalysisCurrentCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.functionTraceAnalysisCurrentCompatible

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.functionTraceAnalysisCurrent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.functionTraceAnalysisCurrent

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.exactConstructorAt?_of_fetch_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.exactConstructorAt?_of_fetch_descendant

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.scalarLeafAt?_of_free_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.scalarLeafAt?_of_free_descendant

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.schema_fields_replicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.schema_fields_replicate

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.schema_fields_replicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.schema_fields_replicate

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteFacts?_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteFacts?_next

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_next' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_next

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_alternative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_alternative

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_root

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_main' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_main

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteFacts?_sourceCodeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteFacts?_sourceCodeAt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteFacts?_alternative_of_sourceCodeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteFacts?_alternative_of_sourceCodeAt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_root

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_main' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_main

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_ctor

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natZero

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natSucc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_alternative_natSucc

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next_of_currentCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.siteEnvironmentHolds_next_of_currentCompatible

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_eq_some

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_runtime

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_matches_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.exactConstructorAt?_matches_node

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_eq_some

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_runtime

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_matches_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.scalarLeafAt?_matches_node

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_fetch_state_of_run_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_free_freeUnique_state_of_run_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_functionRoot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.sourceCodeAt?_functionRoot

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.functionEntryTraceState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.functionEntryTraceState

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.declarationFunctionEntryTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.declarationFunctionEntryTraceState

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.mainFunctionEntryTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.mainFunctionEntryTraceState

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.functionEntryTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.functionEntryTraceState

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.initialMainTraceState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.initialMainTraceState

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.initialMainSourceOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.initialMainSourceOwnership

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.traceState_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.traceState_next

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.traceState_next_of_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.traceState_next_of_member

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.mainTraceState_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.mainTraceState_next

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_transfer_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_apply_transfer_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_erased_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_apply_erased_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_under_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_under_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_saturated_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_saturated_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_over_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_over_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_success

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_saturated_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_saturated_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_over_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_over_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_under_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_under_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_erased_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_erased_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_call_fn_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_self_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_call_self_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_fn_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_tail_call_fn_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_self_enter_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_tail_call_self_enter_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_return_to_letOp_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_return_to_letOp_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_halt_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_ret_halt_success

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_pure_move_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_pure_move_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_pure_move_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_pure_move_success_step

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_alloc_checked_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_alloc_checked_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_alloc_checked_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_alloc_checked_success_step

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dup_retain_scalar_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_dup_retain_scalar_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dup_retain_shared_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_dup_retain_shared_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_scalar_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_drop_release_scalar_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_scalar_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_scalar_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_recursive_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_recursive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_drop_release_recursive_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_papp_fn_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_papp_fn_state

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_fetch_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_fetch_state_of_run_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_free_freeUnique_state_of_run_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_free_freeUnique_state_of_run_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.next

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.constructorChild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.constructorChild

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.natZeroChild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.natZeroChild

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.natSuccChild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.TraceStateRel.natSuccChild

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_switch_ctor_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_switch_ctor_state_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_zero_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_zero_state_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_succ_state_hpt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.simulate_traced_switch_nat_succ_state_hpt

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.hptPostFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.hptPostFixpoint

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.hptLocalPostFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.hptLocalPostFixpoint

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.sidecarDeclarationEnvironment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.sidecarDeclarationEnvironment

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.hptSidecarLocalPostFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.hptSidecarLocalPostFixpoint

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.siteEnvironmentHolds_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.siteEnvironmentHolds_next

/-- info: 'Ix.Compiler.IxIR1.resolveAtoms_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.resolveAtoms_length

/-- info: 'Ix.Compiler.IxIR1.runCode_ret_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runCode_ret_success

/-- info: 'Ix.Compiler.IxIR1.runCode_letOp_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runCode_letOp_success

/-- info: 'Ix.Compiler.IxIR1.runOp_pure_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_pure_success

/-- info: 'Ix.Compiler.IxIR1.runOp_alloc_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_alloc_success

/-- info: 'Ix.Compiler.IxIR1.runOp_free_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_free_success

/-- info: 'Ix.Compiler.IxIR1.runOp_fetch_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_fetch_success

/-- info: 'Ix.Compiler.IxIR1.runOp_reuse_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_reuse_success

/-- info: 'Ix.Compiler.IxIR1.runOp_dup_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_dup_success

/-- info: 'Ix.Compiler.IxIR1.runOp_drop_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_drop_success

/-- info: 'Ix.Compiler.IxIR1.runOp_dropU_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_dropU_success

/-- info: 'Ix.Compiler.IxIR1.runOp_call_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_call_success

/-- info: 'Ix.Compiler.IxIR1.runOp_callSelf_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_callSelf_success

/-- info: 'Ix.Compiler.IxIR1.runOp_papp_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_papp_success

/-- info: 'Ix.Compiler.IxIR1.runOp_apply_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_apply_success

/-- info: 'Ix.Compiler.IxIR1.runOp_extern_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_extern_success

/-- info: 'Ix.Compiler.IxIR1.invoke_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.invoke_success

/-- info: 'Ix.Compiler.IxIR1.runCode_case_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runCode_case_success

/-- info: 'Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_map_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_map_fst

/-- info: 'Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_of_find?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.sourceAlternativeAtTag?_of_find?

/-- info: 'Ix.Compiler.IxIR2.Pipeline.indexedCaseSuccess_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.indexedCaseSuccess_of_run

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.allocationSchema_of_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.allocationSchema_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.allocationSchemasMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.allocationSchemasMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Trace.functionAllocationSchemasMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Trace.functionAllocationSchemasMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.allocationSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.allocationSchema

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.allocationSchemaFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.allocationSchemaFields

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.allocationPosition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.allocationPosition_of_capabilities_match

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_coordinateMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_coordinateMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.positionMatches_of_positionsMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.positionMatches_of_positionsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.position_of_positionsMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.position_of_positionsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.positionsMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.positionsMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.positionsMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.positionsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Trace.functionPositionsMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Trace.functionPositionsMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.position

/-- info: 'Ix.Compiler.IxIR2.Lower.BindingCap.matchesParameter' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.BindingCap.matchesParameter

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.parameterCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.parameterCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.capability_of_parameterCapabilitiesMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.capability_of_parameterCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.owned_of_parameterCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.owned_of_parameterCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.positionParameterCapabilitiesMatch_of_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.positionParameterCapabilitiesMatch_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.positionParameterCapabilities_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.positionParameterCapabilities_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.parameterCapabilitiesMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.parameterCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.parameterCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Trace.functionParameterCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Trace.functionParameterCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.ownedParameterCapability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.ownedParameterCapability

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.parameterCapability' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.parameterCapability

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.pureTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.pureTransition_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.pureCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.pureCapabilitiesMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.pureCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.pureCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Trace.functionPureCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Trace.functionPureCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.pureTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.pureTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.dupTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.dupTransition_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.dupCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.dupCapabilitiesMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.dupCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.dupCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Trace.functionDupCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Trace.functionDupCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.dupTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.dupTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.fetchTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.fetchTransition_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.fetchCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.fetchCapabilitiesMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.fetchCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.fetchCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Trace.functionFetchCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Trace.functionFetchCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.fetchTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.fetchTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.retireOwnerCapabilities?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.retireOwnerCapabilities?_size

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.destructionTransition_of_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.destructionTransition_of_match

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.destructionTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.destructionTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.consumeCapability?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.consumeCapability?_size

/-- info: 'Ix.Compiler.IxIR2.Lower.consumeCapabilitiesList?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.consumeCapabilitiesList?_size

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.allocationTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.allocationTransition_of_capabilities_match

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.allocationTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.allocationTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.pappTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.pappTransition_of_capabilities_match

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.pappTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.pappTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.callTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.callTransition_of_capabilities_match

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.callSelfTransition_of_capabilities_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.callSelfTransition_of_capabilities_match

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.callTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.callTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.callSelfTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.callSelfTransition

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_allocationMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.sourceCapabilities_size_of_allocationMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.coordinateMatches_of_allocationMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.coordinateMatches_of_allocationMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.sourceCapability_canConsume_of_allocationMatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.sourceCapability_canConsume_of_allocationMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.allocationCapabilitiesMatch_of_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.allocationCapabilitiesMatch_of_child

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.allocationCapabilitiesMatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.Descendant.allocationCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Trace.functionAllocationCapabilitiesMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Trace.functionAllocationCapabilitiesMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.allocationPosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.allocationPosition

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.empty

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.empty

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.rootsForCapabilities_setDead_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.rootsForCapabilities_setDead_perm

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.rootsForCapabilities_owned_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.rootsForCapabilities_owned_mem

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.focusOwned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.focusOwned

/-- info: 'Ix.Compiler.IxIR2.Lower.PositionTrace.inputReg_of_owned_coordinateMatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.PositionTrace.inputReg_of_owned_coordinateMatch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.OwnedInputRegisters.ofCoordinate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.OwnedInputRegisters.ofCoordinate

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.BorrowSupport.hasWorld' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.BorrowSupport.hasWorld

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.BorrowSupport.monoStore' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.BorrowSupport.monoStore

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.BorrowSupport.ofRestricts' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.BorrowSupport.ofRestricts

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.BorrowProvenance.hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.BorrowProvenance.hasWorld

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.BorrowProvenance.ofRestricts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.BorrowProvenance.ofRestricts

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.move

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.pure

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.CapabilityHolds.incRcStore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.CapabilityHolds.incRcStore

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.dup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.dup

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.dup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.dup

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.fetch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.fetch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.fetch

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.CapabilityHolds.allocNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.CapabilityHolds.allocNode

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.allocationReadyOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.allocationReadyOwnership

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.alloc

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.alloc

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.papp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.papp

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.papp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.papp

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.drop

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.dropU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.dropU

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.free

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.drop

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.dropU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.dropU

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.free

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.RootOwnership_reworldHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.RootOwnership_reworldHead

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.callEntryInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.callEntryInvariant

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.callResultInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.callResultInvariant

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callEntry

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfEntry

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallEntry

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallSelfEntry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.tailCallSelfEntry

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.returnRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.returnRoot

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callResult

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipAt.callSelfResult

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.hasWorld_of_canConsume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.hasWorld_of_canConsume

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtom_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtom_hasWorld

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtoms_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.resolveAtoms_hasWorld

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation_capabilities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.StoreRel.fieldWorlds_of_checked_allocation_capabilities

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_alloc_checked_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_alloc_checked_state

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_alloc_checked_success_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.simulate_traced_alloc_checked_success_step

/-! The continuation-passing whole-trace worker layer stays on the same
audited attachment boundary.  Its finite-step algebra itself needs only
propositional extensionality; attachment-facing cases additionally inherit
the already fenced checked-hash and HPT dependencies. -/

/-- info: 'Ix.Compiler.IxIR2.Pipeline.ReachesPost.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.ReachesPost.refl

/-- info: 'Ix.Compiler.IxIR2.Pipeline.ReachesPost.prepend' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.ReachesPost.prepend

/-- info: 'Ix.Compiler.IxIR2.Pipeline.ReachesPost.step' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.ReachesPost.step

/-- info: 'Ix.Compiler.IxIR2.Pipeline.BudgetedReachesPost.prependPreserving' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.BudgetedReachesPost.prependPreserving

/-- info: 'Ix.Compiler.IxIR2.Pipeline.BudgetedReachesPost.prependFramed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.BudgetedReachesPost.prependFramed

/-- info: 'Ix.Compiler.IxIR2.Pipeline.successfulTraceSimulationAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.successfulTraceSimulationAt_zero

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.haltReturnHandler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.haltReturnHandler

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_pure_move_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_pure_move_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dup_retain_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_dup_retain_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_fetch_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_fetch_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_free_freeUnique_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_free_freeUnique_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_alloc_checked_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_alloc_checked_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_papp_fn_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_papp_fn_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_fn_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_call_fn_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_call_self_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_call_self_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_fn_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_tail_call_fn_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_tail_call_self_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_tail_call_self_cps

/-! Recursive dynamic application composes every return-time dispatcher shape
through the smaller-fuel trace worker. -/

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.functionTrace_of_source_declaration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.functionTrace_of_source_declaration

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.applyMorePlan_of_applyGo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.applyMorePlan_of_applyGo

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_ret_apply_more_pap_over_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_ret_apply_more_pap_over_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_apply_pap_over_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_apply_pap_over_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.applyMoreReturnHandler_of_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.applyMoreReturnHandler_of_plan

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.applyMoreReturnHandler_of_applyGo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.applyMoreReturnHandler_of_applyGo

/-! The validated raw ownership contract crosses final readdressing for the
exact heap image generated by compiled executions. Syntax reflection and the
worker's `SourceStoreImage` invariant retain that image through every source
operation and PAP-entry intermediate, so no arbitrary-final-heap contract is
exposed by the end-to-end interface. -/

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulationSourceContext_eq_addressedCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulationSourceContext_eq_addressedCtx

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.sourceContextRenames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.sourceContextRenames

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.rawApplyOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.rawApplyOwnership

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.applyGo_exactImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.applyGo_exactImage

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.sourceRebuildSemanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.sourceRebuildSemanticAudit

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.sourceCodeAddressImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.sourceCodeAddressImage

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.runOp_preservesSourceStoreImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.runOp_preservesSourceStoreImage

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations

/-! Exact path-local HPT case facts are checked against emitted constructor
targets and reconstruct the runtime switch selection inside the attachment. -/

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.exactCaseTarget_of_switch_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.exactCaseTarget_of_switch_descendant

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_exactHPT_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_exactHPT_nonempty

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_exactHPT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_exactHPT

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_exactHPT_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_exactHPT_runtime

/-! Recursive heap traversal is framed by the continuation's independently
selected suffix budget. -/

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_add_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.releaseSharedWork_add_suffix

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.releaseShared_add_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.releaseShared_add_suffix

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropUniqueWork_add_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropUniqueWork_add_suffix

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.dropUnique_add_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.dropUnique_add_suffix

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_recursive_state_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_drop_release_recursive_state_framed

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_recursive_state_framed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_recursive_state_framed

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_drop_release_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_drop_release_cps

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_dropU_dropUnique_cps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_dropU_dropUnique_cps

/-! The exhaustive attached worker and whole-main endpoint stay within the
same explicit native-hash trust boundary as the checked attachment. -/

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Sidecars.SourceConstructorsValid.runOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Sidecars.SourceConstructorsValid.runOp

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.runOp_preservesSourceStoreImage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.runOp_preservesSourceStoreImage

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_residual_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_residual_nonempty

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.constructorSwitchSelection_of_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.constructorSwitchSelection_of_residual

/-- info: 'Ix.Compiler.IxIR2.Lower.Artifact.mainTraceMember' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Artifact.mainTraceMember

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.simulate_traced_letOp_cps_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.simulate_traced_letOp_cps_of_run

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulTraceSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.successfulTraceSimulation

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.successfulMainSimulation

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.sourceContextNoReuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.sourceContextNoReuse

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.pappSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.pappSafe

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulSimulationContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.successfulSimulationContracts

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulCanonicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.successfulCanonicalMainSimulation

/-! ## Checked block-local liveness

The liveness checker retains its accepted coverage equation, and its public
projections turn that equation into per-use coverage and a no-later-use fact.
The executable fixture's proof wrapper must remain reflection-axiom free. -/

/-- info: 'Ix.Compiler.IxIR2.Liveness.CheckedBlock.coversAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Liveness.CheckedBlock.coversAt

/-- info: 'Ix.Compiler.IxIR2.Liveness.CheckedBlock.no_use_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Liveness.CheckedBlock.no_use_after

/-- info: 'Ix.Compiler.IxIR2.Liveness.Examples.registerTwoNoUseAfter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Liveness.Examples.registerTwoNoUseAfter

/-- info: 'Ix.Compiler.IxIR2.Liveness.Examples.CheckedSuite.accepted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Liveness.Examples.CheckedSuite.accepted

/-! ## Validator-gated dynamic shared reuse insertion

The first compiler-emitted reversal rewrite retains ordinary validation
witnesses for both sides.  Its bounded benchmark checker packages the exact
executed source/baseline/logical/physical Boolean without reflection axioms. -/

/-- info: 'Ix.Compiler.IxIR2.Reuse.Placement.noUseAfter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Placement.noUseAfter

/-- info: 'Ix.Compiler.IxIR2.Reuse.inferPlacementWith_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.inferPlacementWith_sound

/-- info: 'Ix.Compiler.IxIR2.Reuse.representation?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.representation?_sound

/-- info: 'Ix.Compiler.IxIR2.Reuse.reuseShape?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.reuseShape?_sound

/-- info: 'Ix.Compiler.IxIR2.Reuse.candidate?_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.candidate?_sound

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.fits

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.placementCoordinates' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.placementCoordinates

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noUseAfter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noUseAfter

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.instructionCases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.instructionCases

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noCall

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noCallSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noCallSelf

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noApply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noApply

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noMove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noMove

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noFreeUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noFreeUnique

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noPapp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noPapp

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noDropUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noDropUnique

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.noAllocUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.noAllocUnique

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.ne_resetBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.ne_resetBlock

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.candidateCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.candidateCore

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.candidateVectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.candidateVectors

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.resetBlock_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.resetBlock_eq

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.creditBlock_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.creditBlock_eq

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.schemas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.schemas

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.runtimeSchemas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.runtimeSchemas

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.allocationArgumentsFound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.allocationArgumentsFound

/-- info: 'Ix.Compiler.IxIR2.Reuse.Site.tailArgumentsFound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Site.tailArgumentsFound

/-- info: 'Ix.Compiler.IxIR2.Reuse.Output.sourceValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Output.sourceValid

/-- info: 'Ix.Compiler.IxIR2.Reuse.Output.targetValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Output.targetValid

/-- info: 'Ix.Compiler.IxIR2.Reuse.FunctionRewrite.decisionAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.FunctionRewrite.decisionAt

/-- info: 'Ix.Compiler.IxIR2.Reuse.FunctionRewrite.acceptedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.FunctionRewrite.acceptedAt

/-- info: 'Ix.Compiler.IxIR2.Reuse.FunctionRewrite.accepted_target_ne_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.FunctionRewrite.accepted_target_ne_source

/-- info: 'Ix.Compiler.IxIR2.Reuse.DeclarationDecisions.related' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.DeclarationDecisions.related

/-- info: 'Ix.Compiler.IxIR2.Reuse.DeclarationsRel.find?_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.DeclarationsRel.find?_fn

/-- info: 'Ix.Compiler.IxIR2.Reuse.Trace.context_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Trace.context_fn

/-- info: 'Ix.Compiler.IxIR2.Reuse.Output.trace_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Output.trace_target

/-- info: 'Ix.Compiler.IxIR2.Reuse.Output.trace_report' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Output.trace_report

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.translateRegister?_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.translateRegister?_range

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.ValuesRel.pushResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.ValuesRel.pushResult

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.valuesRel_helperEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.valuesRel_helperEntry

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.valuesRel_afterAllocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.valuesRel_afterAllocation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.helperEntryValues_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.helperEntryValues_size

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.branchValues_resolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.branchValues_resolve

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.helperEdgeTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.helperEdgeTransfer

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAtom_translate' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAtom_translate

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAtoms_translate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAtoms_translate

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAllocationArguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAllocationArguments

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveTailArguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveTailArguments

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotLogicalControlPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotLogicalControlPrefix

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPhysicalControlPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPhysicalControlPrefix

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.coldControlPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.coldControlPrefix

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.absentHelperControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.absentHelperControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.logicalPresentHelperControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.logicalPresentHelperControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.physicalPresentHelperControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.physicalPresentHelperControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotReuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotReuse_sound

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.coldPrefix_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.coldPrefix_commutes

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPrefix_contents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPrefix_contents

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPrefixReuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPrefixReuse_sound

/-- info: 'Ix.Compiler.IxIR1.Sim.reuse_shared_sound_with_survivors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.reuse_shared_sound_with_survivors

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.PlannerValueRelevant' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.PlannerValueRelevant

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.PlannerAtomRelevant' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.PlannerAtomRelevant

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.PlannerValueInRoots' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.PlannerValueInRoots

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.MappedValuesInRoots.selfRelated' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.MappedValuesInRoots.selfRelated

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.ValuesRel.toTranslatedValuesIso' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.ValuesRel.toTranslatedValuesIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.TranslatedValuesIso.pushResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.TranslatedValuesIso.pushResult

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAtom_translate_iso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAtom_translate_iso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAtoms_translate_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAtoms_translate_iso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAtom_iso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAtom_iso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAtoms_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAtoms_iso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveAllocationArguments_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveAllocationArguments_iso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.resolveTailArguments_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.resolveTailArguments_iso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.translatedValuesIso_helperEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.translatedValuesIso_helperEntry

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.translatedValuesIso_afterAllocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.translatedValuesIso_afterAllocation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.evalRuntimeSchemas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.evalRuntimeSchemas

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.physicalPresentHelperControlIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.physicalPresentHelperControlIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPhysicalAcceptedControlIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPhysicalAcceptedControlIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.physicalPresentHelperControlTranslated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.physicalPresentHelperControlTranslated

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPhysicalAcceptedControlTranslated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPhysicalAcceptedControlTranslated

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotLogicalAcceptedControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotLogicalAcceptedControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.coldAcceptedControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.coldAcceptedControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.fetchPrefixControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.fetchPrefixControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.retainPrefixControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.retainPrefixControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.baselineAcceptedControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.baselineAcceptedControl

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotReuse_sound_with_survivors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotReuse_sound_with_survivors

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPrefixReuse_sound_with_survivors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPrefixReuse_sound_with_survivors

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPrefixReuse_sound_under_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPrefixReuse_sound_under_iso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotLogicalAcceptedPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotLogicalAcceptedPrefix

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.coldAcceptedPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.coldAcceptedPrefix

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.hotPhysicalAcceptedPrefixIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.hotPhysicalAcceptedPrefixIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedHotLogicalSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedHotLogicalSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedColdSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedColdSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedHotPhysicalSimulationIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedHotPhysicalSimulationIso

/-! The whole-program lift keeps its structural lookup, evaluator transport,
heap congruence, and stable lockstep interfaces inside the ordinary logical
axiom envelope. -/

/-- info: 'Ix.Compiler.IxIR1.Sim.RValIso.eq_of_location_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.RValIso.eq_of_location_eq

/-- info: 'Ix.Compiler.IxIR1.Sim.RValsIso.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.RValsIso.refl

/-- info: 'Ix.Compiler.IxIR1.Sim.RValsIso.eq_of_location_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.RValsIso.eq_of_location_eq

/-- info: 'Ix.Compiler.IxIR2.Eval.FieldWorlds.to_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.FieldWorlds.to_replicate

/-- info: 'Ix.Compiler.IxIR2.Eval.FieldWorlds.congrStore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.FieldWorlds.congrStore

/-- info: 'Ix.Compiler.IxIR2.Eval.FieldValuesWorldEq.length_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.FieldValuesWorldEq.length_eq

/-- info: 'Ix.Compiler.IxIR2.Eval.FieldWorlds.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.FieldWorlds.transport

/-- info: 'Ix.Compiler.IxIR2.Eval.ConstructorView.congrStore' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ConstructorView.congrStore

/-- info: 'Ix.Compiler.IxIR2.Eval.ScalarOracleCall.congrOracle' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ScalarOracleCall.congrOracle

/-- info: 'Ix.Compiler.IxIR2.Eval.ScalarOracleCall.scalar' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.ScalarOracleCall.scalar

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditLookup.congrDefinition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditLookup.congrDefinition

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditTake.congrDefinition' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditTake.congrDefinition

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditTake.target_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditTake.target_eq

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditTakeMany.definition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditTakeMany.definition

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditTakeMany.sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditTakeMany.sequence

/-- info: 'Ix.Compiler.IxIR2.Eval.CreditTakeSequence.toMany' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CreditTakeSequence.toMany

/-- info: 'Ix.Compiler.IxIR2.Eval.EdgeTransfer.parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.EdgeTransfer.parts

/-- info: 'Ix.Compiler.IxIR2.Eval.EdgeTransfer.congrDefinition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.EdgeTransfer.congrDefinition

/-- info: 'Ix.Compiler.IxIR2.Eval.EdgeTransfer.targetBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.EdgeTransfer.targetBlock

/-- info: 'Ix.Compiler.IxIR2.Eval.EdgeTransfer.definition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.EdgeTransfer.definition

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.deterministic' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.deterministic

/-- info: 'Ix.Compiler.IxIR2.Eval.Steps.cancelPrefixToHalted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Steps.cancelPrefixToHalted

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.extern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.extern

/-- info: 'Ix.Compiler.IxIR2.Reuse.Decision.replacement_valueParams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Decision.replacement_valueParams

/-- info: 'Ix.Compiler.IxIR2.Reuse.Decision.replacement_creditParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Decision.replacement_creditParams

/-- info: 'Ix.Compiler.IxIR2.Reuse.FunctionRewrite.blockCase' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.FunctionRewrite.blockCase

/-- info: 'Ix.Compiler.IxIR2.Reuse.FunctionRewrite.blockCaseOfLookup' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.FunctionRewrite.blockCaseOfLookup

/-- info: 'Ix.Compiler.IxIR2.Reuse.FunctionRewrite.targetBlockAbi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.FunctionRewrite.targetBlockAbi

/-- info: 'Ix.Compiler.IxIR2.Reuse.FunctionRewrite.definition_blocks_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.FunctionRewrite.definition_blocks_nonempty

/-- info: 'Ix.Compiler.IxIR2.Reuse.Trace.context_extern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Trace.context_extern

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.rvalHasWorld_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.rvalHasWorld_eq

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.fieldWorlds_iff

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.constructorView' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.constructorView

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.retainShared' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.retainShared

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.retainSharedMany' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.retainSharedMany

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.reserve' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.reserve

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.tickResetAttempt' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.tickResetAttempt

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.tickHotReset' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.tickHotReset

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.tickColdReset' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.tickColdReset

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseReservation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseReservation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.reuseReservation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.reuseReservation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.heapIsoKillShared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.heapIsoKillShared

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.heapIsoKillShared_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.heapIsoKillShared_rel

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.heapIso_rvalHasWorld_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.heapIso_rvalHasWorld_eq

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.heapIso_fieldWorlds_of_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.heapIso_fieldWorlds_of_replicate

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.FieldWorlds.avoidsMissing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.FieldWorlds.avoidsMissing

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseShared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseShared

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.releaseSharedWork_addFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.releaseSharedWork_addFuel

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.releaseSharedWork_remaining_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.releaseSharedWork_remaining_le

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseSharedWork_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseSharedWork_of_le

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.releaseShared_remaining_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.releaseShared_remaining_le

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.releaseShared_addFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.releaseShared_addFuel

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseShared_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.releaseShared_of_le

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.dropUniqueWork_contents_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.dropUniqueWork_contents_congr

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.dropUnique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.dropUnique

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.dropUniqueWork_addFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.dropUniqueWork_addFuel

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.dropUniqueWork_remaining_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.dropUniqueWork_remaining_le

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.dropUnique_addFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.dropUnique_addFuel

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.dropUnique_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.HeapContentsEq.dropUnique_of_le

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.entry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.entry

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.atPosition' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.atPosition

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.blockCase' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.blockCase

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advancePush' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advancePush

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.push' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.push

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advance' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advance

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advanceAppendCredit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advanceAppendCredit

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.values_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.values_eq

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.rewritten_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.rewritten_eq

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advanceTake' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.advanceTake

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.edgeTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.edgeTransfer

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.takeIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.takeIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.takeManyIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.takeManyIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.edgeTransferIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.edgeTransferIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameRel.entry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameRel.entry

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameRel.push' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameRel.push

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameIso.transportRelation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableFrameRel.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableFrameRel.transportRelation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableContinuationIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableContinuationIso.transportRelation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableStackIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableStackIso.transportRelation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableControlIso.recursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableControlIso.recursiveCall

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMachineRel.contentsRecursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMachineRel.contentsRecursiveCall

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMachineRel.isomorphicRecursiveCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMachineRel.isomorphicRecursiveCall

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableContinuationIso.applyMoreOrResume' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableContinuationIso.applyMoreOrResume

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedHotLogicalStableSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedHotLogicalStableSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedColdStableSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedColdStableSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedHotPhysicalStableSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedHotPhysicalStableSimulationIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferErased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferErased

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferPapUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferPapUnder

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferPapFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferPapFn

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferPapExtern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransferPapExtern

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedApplyTransfer

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedApplyStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedApplyStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedApplyStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedApplyStepOfTrace

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedRetApplyMoreStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedRetApplyMoreStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedRetApplyMoreStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedRetApplyMoreStepOfTrace

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedMoveStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedMoveStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedFetchStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedFetchStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedFreeUniqueStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedFreeUniqueStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedAllocStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedAllocStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedAllocWithAbsentStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedAllocWithAbsentStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedAllocWithLogicalStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedAllocWithLogicalStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedAllocWithPhysicalStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedAllocWithPhysicalStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedDiscardCreditAbsentStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedDiscardCreditAbsentStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedDiscardCreditLogicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedDiscardCreditLogicalStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedDiscardCreditPhysicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedDiscardCreditPhysicalStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedTakeUniqueLogicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedTakeUniqueLogicalStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedTakeUniquePhysicalStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedTakeUniquePhysicalStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedResetSharedLogicalHotStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedResetSharedLogicalHotStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedResetSharedPhysicalHotStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedResetSharedPhysicalHotStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedResetSharedColdStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedResetSharedColdStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedCallSelfStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedCallSelfStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedCallFnStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedCallFnStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedPappFnStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedPappFnStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedPappExternStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedPappExternStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedExternStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedExternStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedTailCallSelfStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedTailCallSelfStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedTailCallFnStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedTailCallFnStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedRetResumeStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedRetResumeStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedRetHaltStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedRetHaltStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedJumpStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedJumpStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedSwitchCtorStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedSwitchCtorStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedSwitchNatZeroStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedSwitchNatZeroStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedSwitchNatSuccStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedSwitchNatSuccStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedBranchCreditPresentStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedBranchCreditPresentStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedBranchCreditAbsentStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedBranchCreditAbsentStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedRetainSharedStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedRetainSharedStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedReleaseSharedStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedReleaseSharedStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedDropUniqueStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedDropUniqueStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedInstructionStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedInstructionStepOfTrace

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedInstructionStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedInstructionStepOfTraceIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedTerminatorStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedTerminatorStepOfTrace

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedTerminatorStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedTerminatorStepOfTraceIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedStepOfTrace

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.unchangedStepOfTraceIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.unchangedStepOfTraceIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMacroSimulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMacroSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMacroSimulation.ofStepsOne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMacroSimulation.ofStepsOne

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMachineRel.haltedParts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMachineRel.haltedParts

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMacroInvariantStep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMacroInvariantStep

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMacroInvariantStep.simulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMacroInvariantStep.simulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableMacroSimulation.preserveInvariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableMacroSimulation.preserveInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedHotLogicalStableMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedHotLogicalStableMacroSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedColdStableMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedColdStableMacroSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedHotPhysicalStableMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedHotPhysicalStableMacroSimulationIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.acceptedColdStableMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.acceptedColdStableMacroSimulationIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.stableMacroStepOfTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.stableMacroStepOfTrace

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.stableMacroStepOfTraceIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.stableMacroStepOfTraceIso

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.stableMacroStepOfTraceRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.stableMacroStepOfTraceRel

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.stableFiniteExecutionOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.stableFiniteExecutionOfMacroInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.stableRunMachineOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.stableRunMachineOfMacroInvariant

/-! ## Liveness-indexed reuse/compiler attachment -/

/-- info: 'Ix.Compiler.IxIR2.Liveness.instruction_reg_mem_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Liveness.instruction_reg_mem_blockUses

/-- info: 'Ix.Compiler.IxIR2.Liveness.terminator_reg_mem_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Liveness.terminator_reg_mem_blockUses

/-- info: 'Ix.Compiler.IxIR2.Liveness.mem_blockUses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Liveness.mem_blockUses

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.callRemainingHolds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.callRemainingHolds

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyRemainingHolds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyRemainingHolds

/-- info: 'Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyInputOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Sim.SourceOwnershipInvariant.applyInputOwnership

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AtomLiveFrom.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AtomLiveFrom.mono

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AtomLiveFrom.instruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AtomLiveFrom.instruction

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AtomLiveFrom.terminator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AtomLiveFrom.terminator

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AtomsLiveFrom.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AtomsLiveFrom.mono

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.plannerValueLiveAtAllocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.plannerValueLiveAtAllocation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.plannerValueLiveAtEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.plannerValueLiveAtEntry

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterCases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterCases

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.ofRValsIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.ofRValsIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.advance' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.advance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.mono

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.push

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.append

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtom' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtom

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.resolveAtoms

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.ofStable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.ofStable

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.advance' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.advance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.takeManyIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.takeManyIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.edgeTransferIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.edgeTransferIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.transportRelation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationAvoids.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationAvoids.transportRelation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackAvoids.transportRelation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackAvoids.transportRelation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableContinuationIso.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableContinuationIso.toLive

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableStackIso.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableStackIso.toLive

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AcceptedPrefixInstruction' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AcceptedPrefixInstruction

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AcceptedPrefixInstructionAt' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AcceptedPrefixInstructionAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.AcceptedEntry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.AcceptedEntry

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPcZero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPcZero

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.halted' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.halted

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSameBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSameBlock

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSourceBlockExcluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofSourceBlockExcluded

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallResume

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallSelfResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofCallSelfResume

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofApplyResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofApplyResume

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofMoveAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofMoveAdvance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofFreeUniqueAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofFreeUniqueAdvance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPappAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofPappAdvance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofDropUniqueAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofDropUniqueAdvance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofAllocUniqueAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.ofAllocUniqueAdvance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.valuesAtEntry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveAcceptedEntry.valuesAtEntry

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableMachineRel.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableMachineRel.toLive

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveControlIso.recursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveControlIso.recursiveCall

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel.contentsRecursiveCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel.contentsRecursiveCall

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel.isomorphicRecursiveCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel.isomorphicRecursiveCall

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedMoveStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedMoveStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedFetchStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedFetchStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedFetchPrologueStepsLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedFetchPrologueStepsLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedCallSelfStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedCallSelfStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedCallFnStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedCallFnStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedJumpStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedJumpStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchNatZeroStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchNatZeroStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchNatSuccStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchNatSuccStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchCtorStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchCtorStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchCtorPrologueStepsLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedSwitchCtorPrologueStepsLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedBranchCreditPresentStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedBranchCreditPresentStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedBranchCreditAbsentStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedBranchCreditAbsentStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTailCallSelfStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTailCallSelfStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTailCallFnStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTailCallFnStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetResumeStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetResumeStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetHaltStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetHaltStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AtomsLiveFrom.instruction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AtomsLiveFrom.instruction

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationIso.applyMoreOrResumeIso' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationIso.applyMoreOrResumeIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedFreeUniqueStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedFreeUniqueStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocWithAbsentStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocWithAbsentStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocWithLogicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocWithLogicalStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocWithPhysicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAllocWithPhysicalStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTakeUniqueLogicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTakeUniqueLogicalStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTakeUniquePhysicalStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTakeUniquePhysicalStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedResetSharedLogicalHotStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedResetSharedLogicalHotStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedResetSharedPhysicalHotStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedResetSharedPhysicalHotStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedResetSharedColdStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedResetSharedColdStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetainSharedStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetainSharedStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedReleaseSharedStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedReleaseSharedStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDropUniqueStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDropUniqueStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDiscardCreditAbsentStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDiscardCreditAbsentStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDiscardCreditLogicalStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDiscardCreditLogicalStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDiscardCreditPhysicalStepLiveIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedDiscardCreditPhysicalStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedPappFnStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedPappFnStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedPappExternStepLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedPappExternStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedExternStepLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedExternStepLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferErasedLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferErasedLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferPapUnderLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferPapUnderLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferPapFnLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferPapFnLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferPapExternLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferPapExternLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyTransferLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedApplyStepOfTraceLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetApplyMoreStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedRetApplyMoreStepOfTraceLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedInstructionStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedInstructionStepOfTraceLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAcceptedPrefixInstructionStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedAcceptedPrefixInstructionStepOfTraceLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTerminatorStepOfTraceLiveIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedTerminatorStepOfTraceLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedStepOfTraceLiveIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedStepOfTraceLiveIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveSimulationIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotLogicalStableLiveMacroSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccounting

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccountingAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedHotPhysicalStableLiveMacroSimulationIsoOfAccountingAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIsoAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedColdStableLiveMacroSimulationIsoAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveMacroStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveMacroStepOfTraceIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt.simulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulationAt.simulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep.simulation' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroInvariantStep.simulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveInvariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.ofStepsOne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.ofStepsOne

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableMacroSimulation.toLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableMacroSimulation.toLive

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfMacroInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfGuidedMacroInvariant' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveFiniteExecutionOfGuidedMacroInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveRunMachineOfMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveRunMachineOfMacroInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveRunMachineOfGuidedMacroInvariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.stableLiveRunMachineOfGuidedMacroInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.retainSharedMany_of_rootOwnership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.retainSharedMany_of_rootOwnership

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.retainCtorFields_of_rootOwnership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.retainCtorFields_of_rootOwnership

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.balanceInertRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.balanceInertRoots

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.addInertRoots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.addInertRoots

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.fieldRootPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.fieldRootPartition

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.hotPrefixFieldRootPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.hotPrefixFieldRootPartition

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccounting

/-- info: 'Ix.Compiler.IxIR1.Sim.RootsIso.permuteRight' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.RootsIso.permuteRight

/-- info: 'Ix.Compiler.IxIR1.Sim.HeapIso.rootOwnership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.HeapIso.rootOwnership

/-- info: 'Ix.Compiler.IxIR1.Sim.HeapIso.rootOwnershipPreimageAppend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.Sim.HeapIso.rootOwnershipPreimageAppend

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccountingIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.hotPrefixFieldRootAccountingIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.ValueSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.ValueSupportedByRoots.mono

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.ValueSupportedByRoots.inBounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.ValueSupportedByRoots.inBounds

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.identityOfInBounds' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.identityOfInBounds

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.identityOfInBounds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.identityOfInBounds

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationIso.identityOfSupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationIso.identityOfSupported

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackIso.identityOfSupported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackIso.identityOfSupported

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.ValueSupportedByRoots.avoidsUnitShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.ValueSupportedByRoots.avoidsUnitShared

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameInputCoverage.ofCodeState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameInputCoverage.ofCodeState

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofNoBorrows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofNoBorrows

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSuspension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSuspension

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSelfSuspension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.ofCallSelfSuspension

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.applyPapEntry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.applyPapEntry

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mono

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesInRoots' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesInRoots

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesAtPlannerAllocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveFrameSupportedByRoots.mappedValuesAtPlannerAllocation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.MappedValuesInRoots.preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.MappedValuesInRoots.preimage

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveContinuationSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveContinuationSupportedByRoots.mono

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveStackSupportedByRoots.mono' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveStackSupportedByRoots.mono

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfLive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfLive

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.LiveValuesIso.toHeapIsoOfSupported

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveFrameIso.toHeapIsoOfSupported

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveContinuationIso.toHeapIsoOfSupported

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackIso.toHeapIsoOfSupported' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackIso.toHeapIsoOfSupported

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackIso.avoidsOfSupportedUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveStackIso.avoidsOfSupportedUnit

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.optimizeAttachment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.optimizeAttachment

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackState

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackReturn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackReturn

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerApplyMoreReturn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerApplyMoreReturn

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentOwnership

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.ownedParameterRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.ownedParameterRoot

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRoot

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRootIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceRootIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.coverage

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.activeFrameSupportedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.activeFrameSupportedAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.mappedValuesAtPlannerAllocationOfNoBorrows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.mappedValuesAtPlannerAllocationOfNoBorrows

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.withHeapFuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.withHeapFuel

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.compilerStateOfStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.compilerStateOfStep

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixInstructionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixInstructionAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepPure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepPure

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepFetch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepFetch

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepFreeUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepFreeUnique

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainScalar

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepRetainShared

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.allocationReadyOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.allocationReadyOwnership

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.allocationFieldWorlds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.allocationFieldWorlds

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepAlloc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepAlloc

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepPapp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepPapp

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUniqueScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUniqueScalar

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepDropUnique

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseScalar

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepReleaseShared

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErased

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.externImpossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.externImpossible

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnder

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapExact

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapOver' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterApplyPapOver

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentApply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentApply

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.applyInputOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.applyInputOwnership

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.applyPapPreparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.applyPapPreparation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErasedOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyErasedOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnderOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyPapUnderOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepApplyOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerInstructionCase.resolve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerInstructionCase.resolve

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalInstructionCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalInstructionCase

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalInstructionAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalInstructionAdvance

/-- info: 'Ix.Compiler.IxIR2.Lower.edgeCapabilities?_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.edgeCapabilities?_size

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.constructorBranchSchemaArity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.constructorBranchSchemaArity

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase.compilerMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.CompilerSwitchCtorCase.compilerMacro

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorCaseOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorCaseOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacroOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacroOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerTerminatorSyntax' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerTerminatorSyntax

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminatorSyntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminatorSyntax

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorCase

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase.resolve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerTerminatorCase.resolve

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterBeforeRelease' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.entryLiveParameterBeforeRelease

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueBound

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.Reuse.Site.fetchPrologueHead

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAtOfFetched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAtOfFetched

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedParameterValueLive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedParameterValueLive

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedCtorChildSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedCtorChildSource

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAtOfParameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAtOfParameters

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAtOfParameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAtOfParameters

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetched

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetchedExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfFetchedExecution

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.acceptedCtorChildPhysicalMacroOfExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.acceptedCtorChildPhysicalMacroOfExecution

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfCompilerState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfCompilerState

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalSwitchCtorMacroOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorAdvanceHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalTerminatorAdvanceHistory

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterCall

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterCallSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterCallSelf

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCall

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCallSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.enterTailCallSelf

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatZero

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatSucc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepSwitchNatSucc

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepsSwitchCtor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stepsSwitchCtor

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.switchCtorMacro

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnHalt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnHalt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnResume

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMore

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.heap_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.heap_eq

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.heapClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.heapClosed

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteRetainedFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteRetainedFields

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteParameterCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteParameterCount

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.liveValueInBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.liveValueInBounds

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedEntryValueLive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedEntryValueLive

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stackToHeapIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stackToHeapIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.historyOfContents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.historyOfContents

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stackAvoidsOfSupportedUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.stackAvoidsOfSupportedUnit

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteStackAvoidsOfUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteStackAvoidsOfUnit

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistory

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedHotPhysicalStableLiveMacroSimulationHistoryAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistory

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableLiveMacroSimulationHistoryAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.initial

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerState

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerMacroStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerMacroStep

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.compilerMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.compilerMacro

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacroAt

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPrefixCompilerMacro

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.Steps.deterministic' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.Steps.deterministic

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableState

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.simulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.attach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerAcceptedMacroStepAt.attach

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistory

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofStepsOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofStepsOne

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.prependStepsOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.prependStepsOne

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofUnchangedSwitchCtorPrologue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofUnchangedSwitchCtorPrologue

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofSwitchCtorChildBlockCase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.ofSwitchCtorChildBlockCase

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfCompilerState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableSwitchCtorMacroOfCompilerState

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.prefixStepOfLetOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.prefixStepOfLetOp

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfPcZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfPcZero

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfHalted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfHalted

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallResume

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallSelfResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfCallSelfResume

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfApplyResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedCompilerAdvance.stepOfApplyResume

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerMacroStep.attach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerMacroStep.attach

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfStep

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfPrefixStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIsoOfPrefixStep

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceIso

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceRel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableMacroStepOfTraceRel

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.invariantStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableMacroStep.invariantStep

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveCompiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMacroSimulation.preserveCompiler

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableState.advanceInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.AttachedStableState.advanceInvariant

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableFiniteExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableFiniteExecution

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableFiniteExecutionGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableFiniteExecutionGuided

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableRunMachine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableRunMachine

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableRunMachineGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedStableRunMachineGuided

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.MappedValuesInRoots.transportOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.MappedValuesInRoots.transportOwnership

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceFieldCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedSiteSourceFieldCount

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminalAllocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.currentTerminalAllocation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.acceptedPhysicalStableMacroStepHistoryOfExecution

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepOfTraceRelGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepOfTraceRelGuided

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel.rewrittenRunning' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.StableLiveMachineRel.rewrittenRunning

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepGuided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableMacroStepGuided

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableFiniteExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableFiniteExecution

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableRunMachine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalStableRunMachine

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.initial

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.Examples.leafHotReuseProducesRelatedHeaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.Examples.leafHotReuseProducesRelatedHeaps

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.Examples.linkedHotPrefixProducesRelatedHeaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.Examples.linkedHotPrefixProducesRelatedHeaps

/-- info: 'Ix.Compiler.IxIR2.Reuse.Examples.CheckedBenchmark.accepted' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Examples.CheckedBenchmark.accepted

/-! ## Typed x86-64 v0 semantic skeleton

The target AST's closed-fragment theorems must remain free of ISA or encoder
assumptions.  The executable local step is likewise an ordinary Lean
definition; its stability theorem stays inside the standard logical fence. -/

/-- info: 'Ix.Compiler.X86.Instr.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.X86.Instr.inV0

/-- info: 'Ix.Compiler.X86.Terminator.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.X86.Terminator.inV0

/-- info: 'Ix.Compiler.X86.Program.inV0' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.X86.Program.inV0

/-- info: 'Ix.Compiler.X86.Checked.inV0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Checked.inV0

/-- info: 'Ix.Compiler.X86.step_of_not_running' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.step_of_not_running

/-- info: 'Ix.Compiler.X86.Core.applyIntrinsicResult_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Core.applyIntrinsicResult_rsp

/-- info: 'Ix.Compiler.X86.Core.applyIntrinsicResult_calleeSaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Core.applyIntrinsicResult_calleeSaved

/-! ## First IxIR₂ scalar selection refinement

Successful selector outputs retain their source-validation witness.  The first
physical IxIR₂ move/alias family then refines the System V `rax` leaf result
without adding any ISA, encoder, native-reflection, or FFI axiom. -/

/-- info: 'Ix.Compiler.X86.Select.Output.sourceValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.Output.sourceValid

/-- info: 'Ix.Compiler.X86.Select.select_scalarMoveProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.select_scalarMoveProgram

/-- info: 'Ix.Compiler.X86.Select.scalarMoveRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.scalarMoveRefines

/-- info: 'Ix.Compiler.X86.Select.selectScalarMoveRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.selectScalarMoveRefines

/-! Source execution history through suspended calls and tail transfers. -/

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.refl

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.trans

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.stepOp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.stepOp

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.caseCtor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.caseCtor

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.caseNatZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.caseNatZero

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.caseNatSucc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.caseNatSucc

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.tailCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.tailCall

/-- info: 'Ix.Compiler.IxIR1.ExecutionHistory.tailCallSelf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.ExecutionHistory.tailCallSelf

/-- info: 'Ix.Compiler.IxIR1.invoke_of_body_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.invoke_of_body_run

/-- info: 'Ix.Compiler.IxIR1.runOp_call_of_body_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_call_of_body_run

/-- info: 'Ix.Compiler.IxIR1.runOp_callSelf_of_body_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_callSelf_of_body_run

/-- info: 'Ix.Compiler.IxIR1.applyGo_exact_of_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.applyGo_exact_of_invoke

/-- info: 'Ix.Compiler.IxIR1.applyGo_over_of_invoke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.applyGo_over_of_invoke

/-- info: 'Ix.Compiler.IxIR1.runOp_apply_exact_of_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_apply_exact_of_invoke

/-- info: 'Ix.Compiler.IxIR1.runOp_apply_over_of_invoke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_apply_over_of_invoke

/-- info: 'Ix.Compiler.IxIR1.runOp_immediate_ctx_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_immediate_ctx_eq

/-- info: 'Ix.Compiler.IxIR1.runOp_apply_erased_ctx_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_apply_erased_ctx_eq

/-- info: 'Ix.Compiler.IxIR1.runOp_apply_under_ctx_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR1.runOp_apply_under_ctx_eq

/-- info: 'Ix.Compiler.IxIR2.Lower.CodeTrace.tailCallResult_of_capabilities_match' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.CodeTrace.tailCallResult_of_capabilities_match

/-- info: 'Ix.Compiler.IxIR2.Lower.Checked.tailCallResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Lower.Checked.tailCallResult

/-- info: 'Ix.Compiler.IxIR2.Pipeline.ApplyMorePlan.sourceRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.ApplyMorePlan.sourceRun

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackHistory.advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackHistory.advance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackHistory.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackHistory.complete

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackCompletion.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerStackCompletion.ordinary

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.historyStepOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.historyStepOp

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.historyImmediateOp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.historyImmediateOp

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnCompletion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnCompletion

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnResumeOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnResumeOfTarget

/-! Residual dispatch, whole-main physical reuse, and checked production selection. -/

/-- info: 'Ix.Compiler.IxIR2.Eval.runMachine_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runMachine_steps

/-- info: 'Ix.Compiler.IxIR2.Reuse.sourceValid_of_invalidTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.sourceValid_of_invalidTarget

/-- info: 'Ix.Compiler.IxIR2.Reuse.sourceRejected_of_invalidSource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.sourceRejected_of_invalidSource

/-- info: 'Ix.Compiler.IxIR2.Reuse.Selection.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.Selection.valid

/-- info: 'Ix.Compiler.IxIR2.Reuse.selectCheckedWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Reuse.selectCheckedWith

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.selectAttachment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.selectAttachment

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreTransfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreTransfer

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreOfTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.CompilerRunningState.returnApplyMoreOfTarget

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalCompilerAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.attachedPhysicalCompilerAdvance

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulation

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulation

/-! Baseline interpretation transport and validated source-to-scalar selection. -/

/-- info: 'Ix.Compiler.IxIR2.CreditFree.instructionAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditFree.instructionAt

/-- info: 'Ix.Compiler.IxIR2.Eval.runMain_creditFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runMain_creditFree

/-- info: 'Ix.Compiler.IxIR2.Eval.runMain_success_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runMain_success_unique

/-- info: 'Ix.Compiler.IxIR2.Eval.Steps.addHeapFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Steps.addHeapFuel

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.mainInterpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.mainInterpretation

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.successfulPhysicalMainSimulation

/-- info: 'Ix.Compiler.X86.Select.ScalarApply.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.ScalarApply.runs

/-- info: 'Ix.Compiler.X86.Select.sourceWord?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.sourceWord?_sound

/-- info: 'Ix.Compiler.X86.Select.Output.refinesSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.Output.refinesSuccessfulRun

/-- info: 'Ix.Compiler.X86.Select.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.sourceRefines

/-- info: 'Ix.Compiler.X86.Select.sourceScalarRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Select.sourceScalarRefines

/-! Immediate-list source recursion recovery. The local evaluator theorem
uses the ordinary Lean basis; the addressed wrappers retain the existing
BLAKE3 hash assumption through the canonical derived declaration identity. -/

/-- info: 'Ix.Compiler.IxIR0.Recursion.sourceTuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Recursion.sourceTuple

/-- info: 'Ix.Compiler.IxIR0.Recursion.recursorForwardSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Recursion.recursorForwardSimulation

/-- info: 'Ix.Compiler.IxIR0.Recursion.Recovered.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Recursion.Recovered.forwardSimulation

/-- info: 'Ix.Compiler.IxIR0.Recursion.Selection.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Recursion.Selection.forwardSimulation

/-- info: 'Ix.Compiler.Recursion.Compilation.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Compilation.sourceRefines

/-! Common ownership lowering and source recursion through selected physical
execution. These compose the existing addressed compiler and reuse proofs;
the existing BLAKE3 assumption is unchanged. -/

/-- info: 'Ix.Compiler.Pipeline.LoweredCompilation.exactCompilerContracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.LoweredCompilation.exactCompilerContracts

/-- info: 'Ix.Compiler.Pipeline.LoweredCompilation.addressedOwnedMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.LoweredCompilation.addressedOwnedMain

/-- info: 'Ix.Compiler.IxIR0.Recursion.Recovered.projectionSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Recursion.Recovered.projectionSafe

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalMainSimulation

/-- info: 'Ix.Compiler.Recursion.Lowered.physicalMainSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Lowered.physicalMainSimulation

/-- info: 'Ix.Compiler.Recursion.Compilation.literalSourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Compilation.literalSourceRefines

/-- info: 'Ix.Compiler.Recursion.Compilation.sourceRefinesSelected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Compilation.sourceRefinesSelected

/-! Physical allocation accounting and selected shared-result reclamation.
The machine and heap-transport lemmas use the ordinary Lean basis; source
composition retains exactly the existing addressed BLAKE3 assumption. -/

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.allocationAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.allocationAccounting

/-- info: 'Ix.Compiler.IxIR2.Eval.runMain_allocationAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runMain_allocationAccounting

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableHeapRel.sharedReclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableHeapRel.sharedReclamation

/-- info: 'Ix.Compiler.Pipeline.LoweredCompilation.reclamation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.LoweredCompilation.reclamation

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.baselineSharedReclamation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.baselineSharedReclamation

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainResources

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedSuccessfulSharedResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedSuccessfulSharedResources

/-- info: 'Ix.Compiler.Recursion.Lowered.physicalMainResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Lowered.physicalMainResources

/-- info: 'Ix.Compiler.Recursion.Compilation.sourceRefinesSelectedWithResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Compilation.sourceRefinesSelectedWithResources

/-! Comparative allocation/free laws. Counters remain separate from the
semantic relations; source composition retains the existing axiom basis. -/

/-- info: 'Ix.Compiler.IxIR2.Eval.InstructionTransferCase.allocationEvents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.InstructionTransferCase.allocationEvents

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedStep_allocationDelta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedStep_allocationDelta

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableHeapRel.live_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableHeapRel.live_eq

/-- info: 'Ix.Compiler.IxIR2.Eval.Result.AllocationLaws.of_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Result.AllocationLaws.of_accounting

/-- info: 'Ix.Compiler.IxIR2.Eval.Result.AllocationLaws.reclaimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Result.AllocationLaws.reclaimed

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithAllocationEvents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithAllocationEvents

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithAllocationEvents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithAllocationEvents

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.baselineNoReuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.baselineNoReuses

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainAllocationLaws

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalAllocationLaws

/-- info: 'Ix.Compiler.Recursion.Lowered.physicalMainAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Lowered.physicalMainAllocationLaws

/-- info: 'Ix.Compiler.Recursion.Compilation.sourceRefinesSelectedWithAllocationLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Compilation.sourceRefinesSelectedWithAllocationLaws

/-! Comparative RC and peak-live bounds, including every selected prefix and
complete shared reclamation. The existing axiom basis is unchanged. -/

/-- info: 'Ix.Compiler.IxIR2.Eval.releaseSharedWork_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.releaseSharedWork_observations

/-- info: 'Ix.Compiler.IxIR2.Eval.InstructionTransferCase.rcCharge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.InstructionTransferCase.rcCharge

/-- info: 'Ix.Compiler.IxIR2.Eval.Step.peakRecords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Step.peakRecords

/-- info: 'Ix.Compiler.IxIR2.Eval.runMachine_prefix_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runMachine_prefix_costs

/-- info: 'Ix.Compiler.IxIR2.ReuseSim.StableHeapRel.pendingRC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseSim.StableHeapRel.pendingRC_eq

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.unchangedStep_costDelta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.unchangedStep_costDelta

/-- info: 'Ix.Compiler.IxIR2.Eval.CostDelta.hot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CostDelta.hot

/-- info: 'Ix.Compiler.IxIR2.Eval.CostDelta.cold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.CostDelta.cold

/-- info: 'Ix.Compiler.IxIR2.Eval.Result.CostBounds.reclaimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Result.CostBounds.reclaimed

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithCosts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.OptimizedAttachment.physicalMainSimulationWithCosts

/-- info: 'Ix.Compiler.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithCosts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.ReuseLiveSim.selectedPhysicalMainSimulationWithCosts

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostBounds

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPrefixCostBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPrefixCostBounds

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedPhysicalMainCostLaws

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulPhysicalCostLaws

/-- info: 'Ix.Compiler.Recursion.Lowered.physicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Lowered.physicalMainCostLaws

/-- info: 'Ix.Compiler.Recursion.Compilation.sourceRefinesSelectedWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Recursion.Compilation.sourceRefinesSelectedWithCostLaws

/-! R5: direct-call credit suspension, reservation ownership, actual selected
compiler execution, and closed source-map specialization. -/

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.runMain_v0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.runMain_v0

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.suspendCall_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.suspendCall_iff

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.Step.reservationOwnership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.Step.reservationOwnership

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.Steps.reservationOwnership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.Steps.reservationOwnership

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.runMain_prefix_reservationOwnership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.runMain_prefix_reservationOwnership

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.runMain_allocationAccounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.runMain_allocationAccounting

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.runMachine_prefix_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.runMachine_prefix_costs

/-- info: 'Ix.Compiler.IxIR2.Eval.Policy.runMain_success_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.Policy.runMain_success_unique

/-- info: 'Ix.Compiler.IxIR2.CallReuse.Selection.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CallReuse.Selection.valid

/-- info: 'Ix.Compiler.IxIR2.CallReuse.Sim.simulate_to_halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CallReuse.Sim.simulate_to_halt

/-- info: 'Ix.Compiler.IxIR2.CallReuse.Output.mainSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CallReuse.Output.mainSimulation

/-- info: 'Ix.Compiler.IxIR2.CallReuse.Selection.mainSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CallReuse.Selection.mainSimulation

/-- info: 'Ix.Compiler.Pipeline.LoweredCompilation.owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.LoweredCompilation.owned

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.baselineClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.baselineClosed

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedCallPrefixCostBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedCallPrefixCostBounds

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedCallPhysicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.selectedCallPhysicalMainCostLaws

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulCallPhysicalCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulCallPhysicalCostLaws

/-- info: 'Ix.Compiler.CallReuse.Compilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.CallReuse.Compilation.sourceRefinesWithCostLaws

/-- info: 'Ix.Compiler.IxIR0.MapRecovery.sourceMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MapRecovery.sourceMap

/-- info: 'Ix.Compiler.IxIR0.MapRecovery.targetMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MapRecovery.targetMap

/-- info: 'Ix.Compiler.IxIR0.MapRecovery.Recovered.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MapRecovery.Recovered.forwardSimulation

/-- info: 'Ix.Compiler.IxIR0.MapRecovery.Selection.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MapRecovery.Selection.forwardSimulation

/-- info: 'Ix.Compiler.IxIR0.MapRecovery.Recovered.projectionSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.MapRecovery.Recovered.projectionSafe

/-- info: 'Ix.Compiler.CallReuse.MapLowered.physicalMainCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.CallReuse.MapLowered.physicalMainCostLaws

/-- info: 'Ix.Compiler.CallReuse.MapCompilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.CallReuse.MapCompilation.sourceRefinesWithCostLaws

/-! Static unique source reversal: saturated source modes, consuming emission,
actual SSA execution, every physical prefix, exact costs, and full release. -/

/-- info: 'Ix.Compiler.Pipeline.CertifiedErasure.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.CertifiedErasure.sourceRefines

/-- info: 'Ix.Compiler.IxIR0.RecursorInstance.address_eq_iff_bytes_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.RecursorInstance.address_eq_iff_bytes_eq

/-- info: 'Ix.Compiler.IxIR0.UniqueReverse.Checked.sourceEvaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.UniqueReverse.Checked.sourceEvaluates

/-- info: 'Ix.Compiler.IxIR0.UniqueReverse.Recovered.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.UniqueReverse.Recovered.forwardSimulation

/-- info: 'Ix.Compiler.UniqueReuse.CheckedSource.sourceValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.CheckedSource.sourceValue

/-- info: 'Ix.Compiler.UniqueReuse.ListAt.hasWorld' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.ListAt.hasWorld

/-- info: 'Ix.Compiler.UniqueReuse.ListAt.graph' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.ListAt.graph

/-- info: 'Ix.Compiler.UniqueReuse.consumingLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.consumingLoop

/-- info: 'Ix.Compiler.UniqueReuse.mainExists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.mainExists

/-- info: 'Ix.Compiler.UniqueReuse.consumingMainResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.consumingMainResult

/-- info: 'Ix.Compiler.UniqueReuse.release1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.release1

/-- info: 'Ix.Compiler.UniqueReuse.release2_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.release2_complete

/-- info: 'Ix.Compiler.UniqueReuse.Target.reserveReuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.reserveReuse

/-- info: 'Ix.Compiler.UniqueReuse.Target.reuseAt_peak' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.reuseAt_peak

/-- info: 'Ix.Compiler.UniqueReuse.Target.loopSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.loopSteps

/-- info: 'Ix.Compiler.UniqueReuse.Target.mainSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.mainSteps

/-- info: 'Ix.Compiler.UniqueReuse.Target.mainRuns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.mainRuns

/-- info: 'Ix.Compiler.UniqueReuse.Target.MainResult.reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.MainResult.reclaims

/-- info: 'Ix.Compiler.UniqueReuse.Target.prefixResources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.prefixResources

/-- info: 'Ix.Compiler.UniqueReuse.Target.costLaws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Target.costLaws

/-- info: 'Ix.Compiler.IxIR2.UniqueLower.Translation.forwardSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.UniqueLower.Translation.forwardSimulation

/-- info: 'Ix.Compiler.UniqueReuse.ownedSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.ownedSemantics

/-- info: 'Ix.Compiler.UniqueReuse.backendSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.backendSemantics

/-- info: 'Ix.Compiler.UniqueReuse.Compilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Compilation.sourceRefinesWithCostLaws

/-! Bounded native unique reversal: byte-memory realization, full emitted
entry and release runs, and unchanged source-contract/axiom boundaries. -/

/-- info: 'Ix.Compiler.X86.Memory.read64_write64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Memory.read64_write64

/-- info: 'Ix.Compiler.X86.UniqueExecution.mainAndRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.UniqueExecution.mainAndRelease

/-- info: 'Ix.Compiler.X86.UniqueExecution.NativeList.nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.UniqueExecution.NativeList.nodup

/-- info: 'Ix.Compiler.UniqueReuse.Native.Output.executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Native.Output.executes

/-- info: 'Ix.Compiler.UniqueReuse.Native.Output.costsAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Native.Output.costsAgree

/-- info: 'Ix.Compiler.UniqueReuse.Native.Output.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Native.Output.sourceRefines

/-- info: 'Ix.Compiler.UniqueReuse.Native.SourceNativeResult.witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Native.SourceNativeResult.witness

/-- info: 'Ix.Compiler.UniqueReuse.Native.Execution.mainSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Native.Execution.mainSafe

/-- info: 'Ix.Compiler.UniqueReuse.Native.Execution.releaseSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Native.Execution.releaseSafe

/-! General logical/physical credit refinement, both policies and the whole
instruction language. These bridges add no native hashing or new axioms. -/

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.step_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.step_related

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.prefix_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.prefix_resources

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.runMain_prefix_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.runMain_prefix_resources

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.checked_runMain_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.checked_runMain_refines

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.runMain_v0_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.runMain_v0_refines

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.runMain_refines_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.runMain_refines_independent

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.OutcomeRel.ownership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.OutcomeRel.ownership

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.OutcomeRel.valueGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.OutcomeRel.valueGraph

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.OutcomeRel.reclamation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.OutcomeRel.reclamation

/-- info: 'Ix.Compiler.IxIR2.CreditRefinement.checked_runMain_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.CreditRefinement.checked_runMain_owned

/-! Runtime source application and a single native reversal function. The
native input, validation, execution, and rejection proofs add no semantic
axiom; addressed compiler certificates retain the existing hash axiom. -/

/-- info: 'Ix.Compiler.Sim.apply_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.apply_sim_inlineSharing

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Compilation.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Compilation.sourceRefines

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Compilation.targetRuns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Compilation.targetRuns

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Target.makeInput_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Target.makeInput_valid

/-- info: 'Ix.Compiler.X86.RuntimeExecution.validationSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.validationSteps

/-- info: 'Ix.Compiler.X86.RuntimeExecution.executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.executes

/-- info: 'Ix.Compiler.X86.RuntimeExecution.canonical_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.canonical_executes

/-- info: 'Ix.Compiler.X86.RuntimeExecution.Execution.mainSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.Execution.mainSafe

/-- info: 'Ix.Compiler.X86.RuntimeExecution.Execution.releaseSafe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.Execution.releaseSafe

/-- info: 'Ix.Compiler.X86.RuntimeExecution.lengthRejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.lengthRejects

/-- info: 'Ix.Compiler.X86.RuntimeExecution.capacityRejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.capacityRejects

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.ArgumentRel.graph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.ArgumentRel.graph

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.Output.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.Output.sourceRefines

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.costsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.costsAgree

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.ofNats_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.ofNats_exact

/-- info: 'Ix.Compiler.X86.RuntimeExecution.inputWordsStep_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeExecution.inputWordsStep_eq

/-! Adjacent reserve/reuse counter folding preserves final general-purpose
registers, arena words, and the source-to-object contract without a new semantic axiom. -/

/-- info: 'Ix.Compiler.X86.UniqueCounterFold.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.UniqueCounterFold.state_eq

/-- info: 'Ix.Compiler.X86.UniqueCounterFold.trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.UniqueCounterFold.trace

/-- info: 'Ix.Compiler.X86.UniqueCounterFold.instruction_saving' does not depend on any axioms -/
#guard_msgs in #print axioms Ix.Compiler.X86.UniqueCounterFold.instruction_saving

/-- info: 'Ix.Compiler.X86.RuntimeTarget.controlCost_saving' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.RuntimeTarget.controlCost_saving

/-! Borrowed ABI checking, finite closed-program execution certificates,
source agreement, actual RC/peak laws, and checked baseline fallback. -/

/-- info: 'Ix.Compiler.IxIR2.Borrow.Checked.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Checked.valid

/-- info: 'Ix.Compiler.IxIR2.Borrow.Checked.exactRewrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Checked.exactRewrite

/-- info: 'Ix.Compiler.IxIR2.Borrow.Execution.steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Execution.steps

/-- info: 'Ix.Compiler.IxIR2.Borrow.Improved.preservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Improved.preservation

/-- info: 'Ix.Compiler.IxIR2.Borrow.Improved.resources' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Improved.resources

/-- info: 'Ix.Compiler.IxIR2.Borrow.Selection.fallbackExact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Selection.fallbackExact

/-- info: 'Ix.Compiler.Borrow.Improved.sourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Improved.sourcePreservation

/-- info: 'Ix.Compiler.Borrow.Improved.resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Improved.resources

/-- info: 'Ix.Compiler.Borrow.Selection.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Selection.valid

/-- info: 'Ix.Compiler.Borrow.Selection.fallbackExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Selection.fallbackExact

/-! Open borrowed functions: structurally derived calls and continuations,
exact lender-store preservation, arbitrary owned input reclamation, and
the actual source-to-runtime composition. No input replay selects a variant. -/

/-- info: 'Ix.Compiler.IxIR2.Borrow.Open.retain_release_cancel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Open.retain_release_cancel

/-- info: 'Ix.Compiler.IxIR2.Borrow.Open.Entry.steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Open.Entry.steps

/-- info: 'Ix.Compiler.IxIR2.Borrow.Open.Entry.lenderLifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Open.Entry.lenderLifetime

/-- info: 'Ix.Compiler.IxIR2.Borrow.Open.Entry.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Open.Entry.total

/-- info: 'Ix.Compiler.IxIR2.Borrow.Open.Certificate.strictImprovement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Open.Certificate.strictImprovement

/-- info: 'Ix.Compiler.IxIR2.Borrow.Open.Certificate.controlCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Open.Certificate.controlCost

/-- info: 'Ix.Compiler.IxIR2.Borrow.Open.Certificate.runFunctions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Borrow.Open.Certificate.runFunctions

/-- info: 'Ix.Compiler.Borrow.Runtime.Source.Shape.applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Source.Shape.applies

/-- info: 'Ix.Compiler.Borrow.Runtime.Tree.counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Tree.counts

/-- info: 'Ix.Compiler.Borrow.Runtime.Argument.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Argument.input

/-- info: 'Ix.Compiler.Borrow.Runtime.Certified.sourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Certified.sourcePreservation

/-- info: 'Ix.Compiler.Borrow.Runtime.Certified.runtimePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Certified.runtimePreservation

/-- info: 'Ix.Compiler.Borrow.Runtime.Certified.sourceToRuntime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Certified.sourceToRuntime

/-- info: 'Ix.Compiler.Borrow.Runtime.Selection.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Selection.valid

/-- info: 'Ix.Compiler.Borrow.Runtime.Selection.fallbackExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Borrow.Runtime.Selection.fallbackExact

/-! E1 consumes actual emitted bytes through an independent parser. All local
encoding, flag, memory-fault and control laws use only the ordinary logical
axioms; whole-stream layout and reference ISA agreement remain separate. -/

/-- info: 'Ix.Compiler.X86.Encode.instruction_decodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.instruction_decodeAt

/-- info: 'Ix.Compiler.X86.Encode.terminator_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.terminator_decode

/-- info: 'Ix.Compiler.X86.Encode.encoded_instruction_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.encoded_instruction_execution

/-- info: 'Ix.Compiler.X86.Encode.compare_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.compare_execution

/-- info: 'Ix.Compiler.X86.Encode.branch_bytes_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.branch_bytes_execution

/-- info: 'Ix.Compiler.X86.Encode.branch_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.branch_patch

/-- info: 'Ix.Compiler.X86.Encode.call_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.call_pair

/-- info: 'Ix.Compiler.X86.Encode.call_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.call_fault

/-- info: 'Ix.Compiler.X86.Encode.ret_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.ret_pair

/-- info: 'Ix.Compiler.X86.Encode.relative_resolves_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.relative_resolves_base

/-- info: 'Ix.Compiler.X86.Encode.patchSigned32_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.patchSigned32_splice

/-- info: 'Ix.Compiler.X86.Encode.signed32_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Encode.signed32_checked

/-! E2 composes complete streams, explicit call-slot memory correspondence,
independent ELF interpretation, PC32 relocation and the emitted N2 source
endpoint. Only indexed source claims retain the existing native hash axiom. -/

/-- info: 'Ix.Compiler.X86.Stream.pcOffset_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.pcOffset_injective

/-- info: 'Ix.Compiler.X86.Stream.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.check_sound

/-- info: 'Ix.Compiler.X86.Stream.linear_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.linear_step

/-- info: 'Ix.Compiler.X86.Stream.branch_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.branch_at

/-- info: 'Ix.Compiler.X86.Stream.call_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.call_progress

/-- info: 'Ix.Compiler.X86.Stream.ret_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.ret_progress

/-- info: 'Ix.Compiler.X86.Stream.run_to_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.run_to_return

/-- info: 'Ix.Compiler.X86.Stream.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.run_with_calls

/-- info: 'Ix.Compiler.X86.Stream.run_permissions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Stream.run_permissions

/-- info: 'Ix.Compiler.X86.StreamExamples.reused_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.StreamExamples.reused_safe

/-- info: 'Ix.Compiler.X86.StreamExamples.nested_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.StreamExamples.nested_safe

/-- info: 'Ix.Compiler.X86.ELF.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ELF.check_sound

/-- info: 'Ix.Compiler.X86.ELF.Valid.text' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ELF.Valid.text

/-- info: 'Ix.Compiler.X86.ELF.Valid.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ELF.Valid.entry

/-- info: 'Ix.Compiler.X86.ELFLink.pc32_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ELFLink.pc32_call

/-- info: 'Ix.Compiler.X86.ELFLink.Applied.resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ELFLink.Applied.resolves

/-- info: 'Ix.Compiler.X86.ELFLink.runtime_call_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ELFLink.runtime_call_transfer

/-- info: 'Ix.Compiler.X86.ObjectEval.run_from_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ObjectEval.run_from_typed

/-- info: 'Ix.Compiler.X86.ObjectEval.run_with_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ObjectEval.run_with_calls

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.Output.emit_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.Output.emit_spec

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.role_callFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.role_callFree

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.Object.provenance_parsed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.Object.provenance_parsed

/-- info: 'Ix.Compiler.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.UniqueReuse.Runtime.Native.Output.sourceRefinesObjects

/-! C3 reuses only equal erased preimages. Closed Nat translation validation
and explicit execution certificates compose with the original source bridge. -/

/-- info: 'Ix.Compiler.IxIR0.Readdress.blockMembers_eq_of_compatibleBlocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.blockMembers_eq_of_compatibleBlocks

/-- info: 'Ix.Compiler.IxIR0.Readdress.members_eq_of_compatibleBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.Readdress.members_eq_of_compatibleBlocks

/-- info: 'Ix.Compiler.IxIR2.Pipeline.Attached.sourcePhysical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.Attached.sourcePhysical

/-- info: 'Ix.Compiler.X86.NatCalls.Output.refinesSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.Output.refinesSuccessfulRun

/-- info: 'Ix.Compiler.X86.NatCalls.Execution.objectReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.Execution.objectReturns

/-- info: 'Ix.Compiler.X86.NatCalls.sourceObjectRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.sourceObjectRefines

/-! C3's static Nat captures preserve exact initializer values and complete
baseline reclamation under the existing closed translation-validation contract. -/

/-- info: 'Ix.Compiler.X86.NatCalls.Expr.closed_evaluate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.Expr.closed_evaluate

/-- info: 'Ix.Compiler.X86.NatCalls.checkCapture' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.checkCapture

/-- info: 'Ix.Compiler.X86.NatCalls.StaticCapture.evaluates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.StaticCapture.evaluates

/-- info: 'Ix.Compiler.X86.NatCalls.Output.reclaimsSuccessfulRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.Output.reclaimsSuccessfulRun

/-- info: 'Ix.Compiler.X86.NatCalls.sourceObjectReclaims' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.NatCalls.sourceObjectReclaims

/-! N3's first scalar slice uses universal source/body, frame, call and
object contracts. Source-indexed theorems retain the existing hash boundary. -/

/-- info: 'Ix.Compiler.X86.ExactNat.encode_some_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ExactNat.encode_some_iff

/-- info: 'Ix.Compiler.X86.ExactNat.add_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ExactNat.add_some_iff

/-- info: 'Ix.Compiler.X86.ExactNat.sub_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ExactNat.sub_toNat

/-- info: 'Ix.Compiler.IxIR0.NatArithmetic.body_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.NatArithmetic.body_applies

/-- info: 'Ix.Compiler.IxIR0.NatArithmetic.sub_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR0.NatArithmetic.sub_applies

/-- info: 'Ix.Compiler.X86.Scalar.Evaluates.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Evaluates.native

/-- info: 'Ix.Compiler.X86.Scalar.Checked.function_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Checked.function_total

/-- info: 'Ix.Compiler.X86.Scalar.Stack.rank_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Stack.rank_capacity

/-- info: 'Ix.Compiler.X86.ObjectEval.run_safeSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.ObjectEval.run_safeSteps

/-- info: 'Ix.Compiler.X86.Scalar.RootRun.objectResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.RootRun.objectResult

/-- info: 'Ix.Compiler.X86.Scalar.Source.programMatches_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Source.programMatches_sound

/-- info: 'Ix.Compiler.X86.Scalar.Source.raw_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Source.raw_evaluates

/-- info: 'Ix.Compiler.X86.Scalar.Source.Selected.sourceApplies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Source.Selected.sourceApplies

/-- info: 'Ix.Compiler.X86.Scalar.Source.Compiled.nativeReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Source.Compiled.nativeReturns

/-- info: 'Ix.Compiler.X86.Scalar.Source.Compiled.sourceReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Source.Compiled.sourceReturns

/-! Compositional selection of actual physical scalar CFGs. -/

/-- info: 'Ix.Compiler.X86.PhysicalScalar.atom_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.atom_sound

/-- info: 'Ix.Compiler.X86.PhysicalScalar.edge_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.edge_transfer

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Runs.call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Runs.call

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Code.simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Code.simulate

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Selected.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Selected.contract

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Runs.agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Runs.agrees

/-- info: 'Ix.Compiler.X86.PhysicalScalar.ExportPath.runMain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.ExportPath.runMain

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Compiled.nativeReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Compiled.nativeReturns

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Compiled.physicalReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Compiled.physicalReturns

/-! Runtime source application through actual physical CFG selection.
Source-indexed contracts retain the existing hash boundary. -/

/-- info: 'Ix.Compiler.Sim.apply_sim_projectionSafe_with_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.apply_sim_projectionSafe_with_members

/-- info: 'Ix.Compiler.Sim.applyMany_sim_projectionSafe_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.Sim.applyMany_sim_projectionSafe_inlineSharing

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.runtimeApply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.runtimeApply

/-- info: 'Ix.Compiler.Pipeline.ValidatedCompilation.runtimeTraceRenames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.Pipeline.ValidatedCompilation.runtimeTraceRenames

/-- info: 'Ix.Compiler.IxIR2.Eval.runFunction_creditFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Eval.runFunction_creditFree

/-- info: 'Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulFunctionSimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.IxIR2.Pipeline.CompiledAttachment.successfulFunctionSimulation

/-- info: 'Ix.Compiler.X86.PhysicalScalar.closureStore.applied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.closureStore.applied

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Exported.sourceFunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Exported.sourceFunction

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Exported.sourceRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Exported.sourceRun

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Exported.sourceReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Exported.sourceReturns

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Exported.sourceNatReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Exported.sourceNatReturns

/-! Captured scalar exports: checked closed initialization, capture binding,
complete reclamation, and universal source-to-object composition. -/

/-- info: 'Ix.Compiler.X86.Scalar.Bound.evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.Scalar.Bound.evaluates

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Heap.owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Heap.owned

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Heap.spent_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Heap.spent_empty

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Heap.applied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Heap.applied

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.checkInitializer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.checkInitializer

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Initialized.reclaimed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Initialized.reclaimed

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.nativeReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.nativeReturns

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.physicalReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.physicalReturns

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceFunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceFunction

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceRun

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceReturns

/-- info: 'Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceNatReturns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Ix.Compiler.X86.PhysicalScalar.Captured.Compiled.sourceNatReturns
