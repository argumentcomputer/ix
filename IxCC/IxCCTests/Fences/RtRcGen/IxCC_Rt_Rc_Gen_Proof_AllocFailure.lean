import IxCC.Rt.Rc.Gen.Proof.AllocFailure

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.reserve_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.reserve_short

/-- info: 'IxCC.Rt.Rc.Gen.alloc_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.alloc_short
