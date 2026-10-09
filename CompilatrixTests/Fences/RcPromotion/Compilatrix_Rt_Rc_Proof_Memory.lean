import Compilatrix.Rt.Rc.Proof.Memory

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.countAddress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.countAddress

/-- info: 'Compilatrix.Rt.Rc.Procs.storeCount_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.storeCount_bytes

/-- info: 'Compilatrix.Rt.Rc.Procs.storeCount_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.storeCount_frame

/-- info: 'Compilatrix.Rt.Rc.Procs.storeCount_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.storeCount_word
