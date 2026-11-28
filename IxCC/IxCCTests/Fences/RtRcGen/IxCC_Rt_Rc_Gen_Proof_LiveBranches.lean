import IxCC.Rt.Rc.Gen.Proof.LiveBranches

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.dynamic_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.dynamic_branch

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.pointer_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.pointer_branch

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.shared_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.shared_branch
