import Compilatrix.Rt.Rc.Proof.DetachHeap

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.HeapLive.detach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.HeapLive.detach

/-- info: 'Compilatrix.Rt.Rc.Procs.free_live_old' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.free_live_old
