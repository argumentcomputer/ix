import Compilatrix.Borrow.Pipeline
import Compilatrix.Borrow.Runtime
import Compilatrix.Borrow.RuntimeInput
import Compilatrix.Borrow.RuntimeSim
import Compilatrix.Borrow.RuntimeSource

/-! Required axiom fences for Borrow; expected messages are preserved verbatim. -/

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
