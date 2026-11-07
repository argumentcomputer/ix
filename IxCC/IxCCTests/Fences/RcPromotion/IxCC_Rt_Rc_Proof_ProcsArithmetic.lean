import IxCC.Rt.Rc.Proof.ProcsArithmetic

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.continuation_field_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.continuation_field_bounds

/-- info: 'IxCC.Rt.Rc.Procs.continuation_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.continuation_next

/-- info: 'IxCC.Rt.Rc.Procs.first_child_pending' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.first_child_pending

/-- info: 'IxCC.Rt.Rc.Procs.increment_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.increment_encoding

/-- info: 'IxCC.Rt.Rc.Procs.increment_overflow_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.increment_overflow_boundary

/-- info: 'IxCC.Rt.Rc.Procs.resumed_child_pending' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.resumed_child_pending

/-- info: 'IxCC.Rt.Rc.Procs.shared_decrement_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.shared_decrement_encoding
