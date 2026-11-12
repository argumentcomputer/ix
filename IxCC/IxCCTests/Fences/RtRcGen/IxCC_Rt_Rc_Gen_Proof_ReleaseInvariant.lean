import IxCC.Rt.Rc.Gen.Proof.ReleaseInvariant

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.Balance.drop_scalars' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.Balance.drop_scalars

/-- info: 'IxCC.Rt.Rc.Gen.PendingCursor.suffix_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.PendingCursor.suffix_scalars

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.cursor_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.cursor_bytes

/-- info: 'IxCC.Rt.Rc.Gen.dropAll_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.dropAll_scalars

/-- info: 'IxCC.Rt.Rc.Gen.live_ne_free' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.live_ne_free

/-- info: 'IxCC.Rt.Rc.Gen.noScalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.noScalars

/-- info: 'IxCC.Rt.Rc.Gen.pending_ne_free' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.pending_ne_free

/-- info: 'IxCC.Rt.Rc.Gen.refsIn_scalars' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.refsIn_scalars
