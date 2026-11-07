import IxCC.Rt.Rc.Proof.ObjectFrame

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.LiveCell.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.LiveCell.frame

/-- info: 'IxCC.Rt.Rc.Procs.ObjectFrame.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ObjectFrame.trans

/-- info: 'IxCC.Rt.Rc.Procs.ObjectFrame.word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ObjectFrame.word

/-- info: 'IxCC.Rt.Rc.Procs.objectFrame_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.objectFrame_write
