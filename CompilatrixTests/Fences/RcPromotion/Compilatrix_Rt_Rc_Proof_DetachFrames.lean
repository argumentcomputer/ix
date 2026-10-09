import Compilatrix.Rt.Rc.Proof.DetachFrames

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.CursorChain.free_cell' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.CursorChain.free_cell

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_cursor_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_cursor_frame

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_slot_frame
