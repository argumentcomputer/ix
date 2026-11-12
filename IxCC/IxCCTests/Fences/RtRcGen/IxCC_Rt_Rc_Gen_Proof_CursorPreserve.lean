import IxCC.Rt.Rc.Gen.Proof.CursorPreserve

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.PendingCursor.advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.PendingCursor.advance

/-- info: 'IxCC.Rt.Rc.Gen.PendingCursor.bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.PendingCursor.bytes

/-- info: 'IxCC.Rt.Rc.Gen.PendingCursor.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.PendingCursor.frame
