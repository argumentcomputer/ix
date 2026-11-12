import IxCC.Rt.Rc.Gen.Proof.AdvanceFrames

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_live

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_slot_frame

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.frame_live_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.frame_live_slots
