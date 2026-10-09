import Compilatrix.Rt.Rc.Proof.IncrementCaller

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.inc_call_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.inc_call_free

/-- info: 'Compilatrix.Rt.Rc.Procs.increment_caller_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.increment_caller_complete
