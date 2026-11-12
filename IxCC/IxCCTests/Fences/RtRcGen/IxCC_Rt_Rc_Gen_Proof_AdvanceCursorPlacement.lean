import IxCC.Rt.Rc.Gen.Proof.AdvanceCursorPlacement

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_cursors_placed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_cursors_placed

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_pending_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.advance_pending_exact
