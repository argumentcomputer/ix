import Compilatrix.Rt.Rc.Proof.CountFrames

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.CursorChain.update_count' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.CursorChain.update_count

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.count_cursor_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.count_cursor_frame

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.count_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.count_slot_frame
