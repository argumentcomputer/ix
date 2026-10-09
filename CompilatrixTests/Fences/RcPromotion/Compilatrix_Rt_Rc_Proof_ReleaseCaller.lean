import Compilatrix.Rt.Rc.Proof.ReleaseCaller

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.dec_call_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.dec_call_free

/-- info: 'Compilatrix.Rt.Rc.Procs.release_caller_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.release_caller_complete
