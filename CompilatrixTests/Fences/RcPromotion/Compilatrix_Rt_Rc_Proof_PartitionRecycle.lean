import Compilatrix.Rt.Rc.Proof.PartitionRecycle

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ArenaPartition.address_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ArenaPartition.address_unique

/-- info: 'Compilatrix.Rt.Rc.Procs.ArenaPartition.disjoint_members' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ArenaPartition.disjoint_members

/-- info: 'Compilatrix.Rt.Rc.Procs.ArenaPartition.recycle_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ArenaPartition.recycle_pending
