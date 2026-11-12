import IxCC.Rt.Rc.Gen.Proof.FrameReleaseCaller

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.dec_call_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.dec_call_free

/-- info: 'IxCC.Rt.Rc.Gen.release_caller_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.release_caller_complete

/-- info: 'IxCC.Rt.Rc.Gen.release_caller_complete_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.release_caller_complete_frame
