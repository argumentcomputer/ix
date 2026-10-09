import Compilatrix.Rt.Rc.Proof.CutpointRank

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.cutpoint_recycle_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.cutpoint_recycle_decreases

/-- info: 'Compilatrix.Rt.Rc.Procs.cutpoint_release_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.cutpoint_release_decreases

/-- info: 'Compilatrix.Rt.Rc.Procs.cutpoint_resume_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.cutpoint_resume_decreases

/-- info: 'Compilatrix.Rt.Rc.Procs.cutpoint_tokens' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.cutpoint_tokens
