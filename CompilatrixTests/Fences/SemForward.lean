import Compilatrix.Sem.Forward

/-! Required axiom fences for forward diagrams and lock steps (M2.5):
`Sem.Forward` (no obligation at a stuck source, resource failures allowed
at the target) and the simulation it gives, and `Sem.LockStep` with
`reaches` and `comp`. Generated from the module's public theorems; expected
messages are preserved verbatim. -/

/-- info: 'Compilatrix.Sem.Forward.TimeoutOrFail.down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Forward.TimeoutOrFail.down

/-- info: 'Compilatrix.Sem.Forward.TimeoutOrFail.star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Forward.TimeoutOrFail.star

/-- info: 'Compilatrix.Sem.Forward.TimeoutOrFail.of_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Forward.TimeoutOrFail.of_fails

/-- info: 'Compilatrix.Sem.Forward.reaches_of_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Forward.reaches_of_fails

/-- info: 'Compilatrix.Sem.Forward.forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Forward.forward

/-- info: 'Compilatrix.Sem.Forward.timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Forward.timeout

/-- info: 'Compilatrix.Sem.Forward.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.Forward.sim

/-- info: 'Compilatrix.Sem.LockStep.reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sem.LockStep.reaches

/-- info: 'Compilatrix.Sem.LockStep.star_through' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.LockStep.star_through

/-- info: 'Compilatrix.Sem.LockStep.comp' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Sem.LockStep.comp
