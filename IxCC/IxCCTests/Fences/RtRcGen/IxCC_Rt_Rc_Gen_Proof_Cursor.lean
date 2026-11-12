import IxCC.Rt.Rc.Gen.Proof.Cursor

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.PendingCursor.next_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.PendingCursor.next_child

/-- info: 'IxCC.Rt.Rc.Gen.PendingParent.cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.PendingParent.cursor

/-- info: 'IxCC.Rt.Rc.Gen.cursor_field_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.cursor_field_address
