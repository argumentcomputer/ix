import Compilatrix.Rt.Rc.Proof.RecycleClasses

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.pending_not_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.pending_not_free

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_distinct

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_free_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_free_exact
