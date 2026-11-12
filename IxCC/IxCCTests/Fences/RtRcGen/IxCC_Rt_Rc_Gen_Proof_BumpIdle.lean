import IxCC.Rt.Rc.Gen.Proof.BumpIdle

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.bump_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.bump_idle

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.bump_not_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.bump_not_free
