import IxCC.Rt.Rc.Gen.Proof.RecycleFrames

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.CursorChain.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.CursorChain.frame

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_slot_frame
