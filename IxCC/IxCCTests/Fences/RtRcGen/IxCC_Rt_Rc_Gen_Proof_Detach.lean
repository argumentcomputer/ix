import IxCC.Rt.Rc.Gen.Proof.Detach

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.detach_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.detach_count

/-- info: 'IxCC.Rt.Rc.Gen.scalar_recycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.scalar_recycle

/-- info: 'IxCC.Rt.Rc.Gen.scan_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.scan_branch

/-- info: 'IxCC.Rt.Rc.Gen.unique_detach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.unique_detach
