import IxCC.Rt.Rc.Gen.Proof.DetachPlacement

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_free_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_free_exact

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_free_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.detach_free_placed

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.live_not_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.live_not_free
