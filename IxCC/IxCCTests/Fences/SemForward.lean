import IxCC.Sem.Forward

/-! Required axiom fences for forward diagrams and lock steps:
`Sem.Forward` (no obligation at a stuck source, resource failures allowed
at the target) and the simulation it gives, and `Sem.LockStep` with
`reaches` and `comp`. Generated from the module's public theorems; expected
messages are preserved verbatim. -/

/-- info: 'IxCC.Sem.Forward.TimeoutOrFail.down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Forward.TimeoutOrFail.down

/-- info: 'IxCC.Sem.Forward.TimeoutOrFail.star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Forward.TimeoutOrFail.star

/-- info: 'IxCC.Sem.Forward.TimeoutOrFail.of_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Forward.TimeoutOrFail.of_fails

/-- info: 'IxCC.Sem.Forward.reaches_of_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Forward.reaches_of_fails

/-- info: 'IxCC.Sem.Forward.forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Forward.forward

/-- info: 'IxCC.Sem.Forward.timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Forward.timeout

/-- info: 'IxCC.Sem.Forward.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Forward.sim

/-- info: 'IxCC.Sem.LockStep.reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.LockStep.reaches

/-- info: 'IxCC.Sem.LockStep.star_through' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.LockStep.star_through

/-- info: 'IxCC.Sem.LockStep.comp' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.LockStep.comp
