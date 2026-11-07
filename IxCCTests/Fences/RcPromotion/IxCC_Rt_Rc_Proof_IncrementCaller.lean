import IxCC.Rt.Rc.Proof.IncrementCaller

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.inc_call_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.inc_call_free

/-- info: 'IxCC.Rt.Rc.Procs.increment_caller_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.increment_caller_complete
