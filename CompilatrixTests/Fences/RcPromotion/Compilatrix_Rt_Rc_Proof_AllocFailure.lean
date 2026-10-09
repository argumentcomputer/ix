import Compilatrix.Rt.Rc.Proof.AllocFailure

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.AllocatorReady.reserve_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.AllocatorReady.reserve_short

/-- info: 'Compilatrix.Rt.Rc.Procs.alloc_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.alloc_short
