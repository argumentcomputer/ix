import IxCC.Rt.Rc.Gen.Proof.AllocFree

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.alloc_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.alloc_free

/-- info: 'IxCC.Rt.Rc.Gen.alloc_free_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.alloc_free_initial

/-- info: 'IxCC.Rt.Rc.Gen.layout_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.layout_class

/-- info: 'IxCC.Rt.Rc.Gen.reserveFree_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.reserveFree_word
