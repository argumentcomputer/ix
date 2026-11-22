import IxCC.Rt.Rc.Gen.Proof.PartitionRecycle

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ArenaPartition.address_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ArenaPartition.address_unique

/-- info: 'IxCC.Rt.Rc.Gen.ArenaPartition.disjoint_members' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ArenaPartition.disjoint_members

/-- info: 'IxCC.Rt.Rc.Gen.ArenaPartition.recycle_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ArenaPartition.recycle_pending
