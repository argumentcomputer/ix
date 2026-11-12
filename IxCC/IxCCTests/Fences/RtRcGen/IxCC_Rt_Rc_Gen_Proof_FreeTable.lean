import IxCC.Rt.Rc.Gen.Proof.FreeTable

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_heads

/-- info: 'IxCC.Rt.Rc.Gen.freeHead_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.freeHead_disjoint

/-- info: 'IxCC.Rt.Rc.Gen.freeHead_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.freeHead_toNat
