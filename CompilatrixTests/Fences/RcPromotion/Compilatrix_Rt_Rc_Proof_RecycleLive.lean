import Compilatrix.Rt.Rc.Proof.RecycleLive

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.finished_parent_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.finished_parent_step

/-- info: 'Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.ReleaseInvariant.recycle_live
