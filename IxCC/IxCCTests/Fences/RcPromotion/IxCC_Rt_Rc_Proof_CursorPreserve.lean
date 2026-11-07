import IxCC.Rt.Rc.Proof.CursorPreserve

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.PendingCursor.advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.PendingCursor.advance

/-- info: 'IxCC.Rt.Rc.Procs.PendingCursor.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.PendingCursor.frame
