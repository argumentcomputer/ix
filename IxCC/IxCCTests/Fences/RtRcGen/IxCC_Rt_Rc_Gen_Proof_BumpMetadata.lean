import IxCC.Rt.Rc.Gen.Proof.BumpMetadata

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.after_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.after_bump

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.limit_address_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.limit_address_nat
