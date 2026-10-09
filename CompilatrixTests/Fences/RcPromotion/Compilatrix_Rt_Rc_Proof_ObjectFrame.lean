import Compilatrix.Rt.Rc.Proof.ObjectFrame

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.LiveCell.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.LiveCell.frame

/-- info: 'Compilatrix.Rt.Rc.Procs.ObjectFrame.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ObjectFrame.trans

/-- info: 'Compilatrix.Rt.Rc.Procs.ObjectFrame.word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ObjectFrame.word

/-- info: 'Compilatrix.Rt.Rc.Procs.objectFrame_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.objectFrame_write
