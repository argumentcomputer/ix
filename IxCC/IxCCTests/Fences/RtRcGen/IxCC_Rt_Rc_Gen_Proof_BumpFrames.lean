import IxCC.Rt.Rc.Gen.Proof.BumpFrames

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.bump_address_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.bump_address_nat

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.bump_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.bump_live

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.bump_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.bump_slot_frame
