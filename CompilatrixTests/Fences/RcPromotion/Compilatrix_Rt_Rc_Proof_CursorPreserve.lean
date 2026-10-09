import Compilatrix.Rt.Rc.Proof.CursorPreserve

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.PendingCursor.advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.PendingCursor.advance

/-- info: 'Compilatrix.Rt.Rc.Procs.PendingCursor.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.PendingCursor.frame
