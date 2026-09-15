import Compilatrix.CallReuse.MapSim
import Compilatrix.CallReuse.Sim
import Compilatrix.CallReuse.SpaceSim

/-! Required axiom fences for CallReuse; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.CallReuse.Compilation.sourceRefinesWithCostLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.CallReuse.Compilation.sourceRefinesWithCostLaws

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

/-- info: 'Compilatrix.IxIR2.Eval.Space.release_committedBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR2.Eval.Space.release_committedBytes

/-- info: 'Compilatrix.CallReuse.MapLowered.finite_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.CallReuse.MapLowered.finite_refines

/-- info: 'Compilatrix.CallReuse.MapCompilation.finite_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.CallReuse.MapCompilation.finite_refines
