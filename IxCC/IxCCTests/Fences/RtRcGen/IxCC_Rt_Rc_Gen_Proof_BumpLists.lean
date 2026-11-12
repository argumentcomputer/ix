import IxCC.Rt.Rc.Gen.Proof.BumpLists

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.bump_chains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.bump_chains

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.bump_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.bump_heads
