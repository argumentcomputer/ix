import IxCC.Rt.Rc.Gen.Proof.FrameReleaseEntry

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.begin_release' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.begin_release

/-- info: 'IxCC.Rt.Rc.Gen.release_entry_complete_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.release_entry_complete_frame
