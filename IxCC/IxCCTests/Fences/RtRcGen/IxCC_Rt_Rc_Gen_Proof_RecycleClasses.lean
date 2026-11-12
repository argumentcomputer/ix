import IxCC.Rt.Rc.Gen.Proof.RecycleClasses

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.pending_not_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.pending_not_free

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_distinct

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_free_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_free_exact
