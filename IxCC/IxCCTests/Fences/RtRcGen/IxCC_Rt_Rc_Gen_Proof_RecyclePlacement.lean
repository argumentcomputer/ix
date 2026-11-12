import IxCC.Rt.Rc.Gen.Proof.RecyclePlacement

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_chains

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_cursors_placed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_cursors_placed

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_free_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_free_placed

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_pending_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_pending_exact
