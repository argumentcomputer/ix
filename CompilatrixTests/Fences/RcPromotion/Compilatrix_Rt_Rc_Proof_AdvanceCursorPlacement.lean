import Compilatrix.Rt.Rc.Proof.AdvanceCursorPlacement

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_cursors_placed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_cursors_placed

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_pending_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.advance_pending_exact
