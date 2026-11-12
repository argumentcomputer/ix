import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.AllocatorReady.after_protected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.AllocatorReady.after_protected

/-- info: 'IxCC.Rt.Rc.Gen.headAddress_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.headAddress_eq
