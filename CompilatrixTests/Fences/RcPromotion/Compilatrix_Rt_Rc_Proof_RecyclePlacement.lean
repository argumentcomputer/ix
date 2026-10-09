import Compilatrix.Rt.Rc.Proof.RecyclePlacement

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_chains

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_cursors_placed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_cursors_placed

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_free_placed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_free_placed

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_pending_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_pending_exact
