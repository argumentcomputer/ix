import IxCC.Rt.Rc.Gen.Proof.AllocatorAccess

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.slot_access' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.slot_access

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.slot_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.slot_nonzero
