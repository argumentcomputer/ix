import IxCC.Rt.Rc.Proof.AllocFree

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.alloc_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.alloc_free

/-- info: 'IxCC.Rt.Rc.Procs.alloc_free_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.alloc_free_initial

/-- info: 'IxCC.Rt.Rc.Procs.reserveFree_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.reserveFree_word
