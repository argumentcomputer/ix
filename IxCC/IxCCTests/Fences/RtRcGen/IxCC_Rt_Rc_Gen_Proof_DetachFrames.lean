import IxCC.Rt.Rc.Gen.Proof.DetachFrames

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.CursorChain.free_cell' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.CursorChain.free_cell

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_cursor_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_cursor_frame

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_slot_frame
