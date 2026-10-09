import Compilatrix.Rt.Rc.Proof.ProcsArithmetic

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.continuation_field_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.continuation_field_bounds

/-- info: 'Compilatrix.Rt.Rc.Procs.continuation_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.continuation_next

/-- info: 'Compilatrix.Rt.Rc.Procs.first_child_pending' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.first_child_pending

/-- info: 'Compilatrix.Rt.Rc.Procs.increment_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.increment_encoding

/-- info: 'Compilatrix.Rt.Rc.Procs.increment_overflow_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.increment_overflow_boundary

/-- info: 'Compilatrix.Rt.Rc.Procs.resumed_child_pending' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.resumed_child_pending

/-- info: 'Compilatrix.Rt.Rc.Procs.shared_decrement_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.shared_decrement_encoding
