import Compilatrix.Recursion.Allocation
import Compilatrix.Recursion.Costs
import Compilatrix.Recursion.PhysicalSim
import Compilatrix.Recursion.Resources
import Compilatrix.Recursion.Sim
import Compilatrix.Recursion.Trace

/-! Required axiom fences for Recursion; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Recursion.Compilation.sourceRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Recursion.Compilation.sourceRefines

/-- info: 'Compilatrix.IxIR0.Recursion.Recovered.projectionSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR0.Recursion.Recovered.projectionSafe

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
