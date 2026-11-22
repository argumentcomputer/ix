import IxCC.Rt.Rc.Gen.Proof.FramePointScalar

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ArenaPartition.kill_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ArenaPartition.kill_free

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.scalar_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.scalar_complete

/-- info: 'IxCC.Rt.Rc.Gen.ReleasePoint.scalar_move_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleasePoint.scalar_move_frame

/-- info: 'IxCC.Rt.Rc.Gen.recycle_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.recycle_advance
