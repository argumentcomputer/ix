import IxCC.Rt.Rc.Gen.Proof.ImmediateStep

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.consume_immediate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.consume_immediate

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.immediate_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.immediate_step

/-- info: 'IxCC.Rt.Rc.Gen.valueWord_immediate_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.valueWord_immediate_tag
