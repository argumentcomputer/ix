import IxCC.Rt.Rc.Gen.Proof.LiveHeader

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.class_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.class_byte

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.class_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.class_load

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.scan_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.scan_byte

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.scan_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.scan_load
