import Compilatrix.Modular.Assemble
import Compilatrix.Modular.Check
import Compilatrix.Modular.SourceCheck
import Compilatrix.Modular.Transport

/-! Required axiom fences for Modular; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Sim.PErase.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.PErase.extend

/-- info: 'Compilatrix.Sim.Covered.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.Covered.extend

/-- info: 'Compilatrix.Sim.MemberCoverage.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.MemberCoverage.extend

/-- info: 'Compilatrix.Modular.Compiled.sourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Modular.Compiled.sourcePreservation

/-- info: 'Compilatrix.Modular.SourceCheck.checkKnown_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Modular.SourceCheck.checkKnown_eq

/-- info: 'Compilatrix.Modular.prepareChecked_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Modular.prepareChecked_eq

/-- info: 'Compilatrix.Modular.checkUnitPrepared_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Modular.checkUnitPrepared_eq
