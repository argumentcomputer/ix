import IxCC.Rt.Rc.Gen.Proof.RecycleCursors

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_cursors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_cursors

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_tail_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_tail_frame
