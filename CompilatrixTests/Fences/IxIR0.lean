import Compilatrix.IxIR0.Decode
import Compilatrix.IxIR0.DynamicCost
import Compilatrix.IxIR0.MapRecoverySim
import Compilatrix.IxIR0.MutualBlock
import Compilatrix.IxIR0.NatArithmetic
import Compilatrix.IxIR0.NatRecursors
import Compilatrix.IxIR0.ProjectionFree
import Compilatrix.IxIR0.Readdress
import Compilatrix.IxIR0.ReaddressOracle
import Compilatrix.IxIR0.ReaddressOracleExamples
import Compilatrix.IxIR0.ReaddressProjectionSafe
import Compilatrix.IxIR0.ReaddressSim
import Compilatrix.IxIR0.RecursionSim
import Compilatrix.IxIR0.RecursorModes
import Compilatrix.IxIR0.UniqueReverseSim

/-! Required axiom fences for IxIR0; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.IxIR0.DynamicCost.Eval.ofTrace' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.DynamicCost.Eval.ofTrace

/-- info: 'Compilatrix.IxIR0.DynamicCost.Applies.append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.DynamicCost.Applies.append

/-- info: 'Compilatrix.IxIR0.ProjectionFree.Eval.of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.ProjectionFree.Eval.of_run

/-- info: 'Compilatrix.IxIR0.DynamicCost.Eval.surfaceEvals_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.DynamicCost.Eval.surfaceEvals_le

/-- info: 'Compilatrix.IxIR0.Readdress.evalTransportAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.evalTransportAt

/-- info: 'Compilatrix.IxIR0.Readdress.Ctx.run_mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.Ctx.run_mapAddresses

/-- info: 'Compilatrix.IxIR0.Readdress.ProjectionSafe.Eval.mapAddresses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.ProjectionSafe.Eval.mapAddresses

/-- info: 'Compilatrix.IxIR0.Readdress.Oracle.readdress_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.Oracle.readdress_compatible

/-- info: 'Compilatrix.IxIR0.MutualBlock.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.MutualBlock.semanticAudit_of_run_eq_ok

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

/-- info: 'Compilatrix.IxIR0.Decl.decodePreimage_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Decl.decodePreimage_roundtrip

/-- info: 'Compilatrix.IxIR0.Decl.decodePreimage_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Decl.decodePreimage_canonical

/-- info: 'Compilatrix.IxIR0.Decl.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Decl.preimage_injective

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

/-- info: 'Compilatrix.IxIR0.Readdress.blockMembers_eq_of_compatibleBlocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.blockMembers_eq_of_compatibleBlocks

/-- info: 'Compilatrix.IxIR0.Readdress.members_eq_of_compatibleBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Readdress.members_eq_of_compatibleBlocks

/-- info: 'Compilatrix.IxIR0.NatArithmetic.body_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.NatArithmetic.body_applies

/-- info: 'Compilatrix.IxIR0.NatArithmetic.sub_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.NatArithmetic.sub_applies
