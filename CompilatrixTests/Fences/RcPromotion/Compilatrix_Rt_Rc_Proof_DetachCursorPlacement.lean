import Compilatrix.Rt.Rc.Proof.DetachCursorPlacement

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_cursors_placed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_cursors_placed

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_pending_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.detach_pending_exact

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.live_not_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.live_not_cursor
