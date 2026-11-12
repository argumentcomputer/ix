import IxCC.Rt.Rc.Gen.Proof.ReserveFrames

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_live

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_protected

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_slot_frame
