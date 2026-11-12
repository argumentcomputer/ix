import IxCC.Rt.Rc.Gen.Proof.FrameReleaseLoop

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleasePoint.reaches_empty_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleasePoint.reaches_empty_frame

/-- info: 'IxCC.Rt.Rc.Gen.ReleasePoint.release_complete_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleasePoint.release_complete_frame
