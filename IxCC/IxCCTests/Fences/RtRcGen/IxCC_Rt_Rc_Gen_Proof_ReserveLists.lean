import IxCC.Rt.Rc.Gen.Proof.ReserveLists

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.free_class_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.free_class_unique

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.pop_free_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.pop_free_mem

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_free_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_free_exact

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_free_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.reserve_free_placed
