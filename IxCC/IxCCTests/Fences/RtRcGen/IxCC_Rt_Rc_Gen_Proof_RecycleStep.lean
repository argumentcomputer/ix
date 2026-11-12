import IxCC.Rt.Rc.Gen.Proof.RecycleStep

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.pending_free_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.pending_free_separation

/-- info: 'IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ReleaseInvariant.recycle_chain
