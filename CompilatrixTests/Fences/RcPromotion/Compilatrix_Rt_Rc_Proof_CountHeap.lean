import Compilatrix.Rt.Rc.Proof.CountHeap

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.HeapLive.update_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.HeapLive.update_count

/-- info: 'Compilatrix.Rt.Rc.Procs.count_live_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.count_live_iff
