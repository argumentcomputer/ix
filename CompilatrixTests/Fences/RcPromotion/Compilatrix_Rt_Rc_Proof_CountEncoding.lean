import Compilatrix.Rt.Rc.Proof.CountEncoding

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.increment_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.increment_count

/-- info: 'Compilatrix.Rt.Rc.Procs.shared_decrement_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.shared_decrement_count

/-- info: 'Compilatrix.Rt.Rc.Procs.truncate32_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.truncate32_toNat
