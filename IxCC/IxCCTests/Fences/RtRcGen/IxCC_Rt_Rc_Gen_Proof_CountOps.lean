import IxCC.Rt.Rc.Gen.Proof.CountOps

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.dec_store_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.dec_store_step

/-- info: 'IxCC.Rt.Rc.Gen.dec_sub_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.dec_sub_step

/-- info: 'IxCC.Rt.Rc.Gen.inc_add_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.inc_add_step

/-- info: 'IxCC.Rt.Rc.Gen.inc_store_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.inc_store_step
