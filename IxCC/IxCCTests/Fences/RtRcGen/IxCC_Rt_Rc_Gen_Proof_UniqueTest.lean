import IxCC.Rt.Rc.Gen.Proof.UniqueTest

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.unique_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.unique_initial

/-- info: 'IxCC.Rt.Rc.Gen.unique_immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.unique_immediate

/-- info: 'IxCC.Rt.Rc.Gen.unique_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.unique_cell

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.isUnique_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.isUnique_answer

/-- info: 'IxCC.Rt.Rc.Gen.isUnique_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.isUnique_spec
