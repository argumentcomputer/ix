import IxCC.Rt.Rc.Gen.Proof.DetachCursorPlacement

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_cursors_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_cursors_placed

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_pending_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_pending_exact

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.live_not_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.live_not_cursor
