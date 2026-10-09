import Compilatrix.Rt.Rc.Proof.AllocFree

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.alloc_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.alloc_free

/-- info: 'Compilatrix.Rt.Rc.Procs.alloc_free_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.alloc_free_initial

/-- info: 'Compilatrix.Rt.Rc.Procs.reserveFree_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.reserveFree_word
