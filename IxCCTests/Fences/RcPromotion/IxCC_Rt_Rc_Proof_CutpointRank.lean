import IxCC.Rt.Rc.Proof.CutpointRank

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.cutpoint_recycle_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.cutpoint_recycle_decreases

/-- info: 'IxCC.Rt.Rc.Procs.cutpoint_release_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.cutpoint_release_decreases

/-- info: 'IxCC.Rt.Rc.Procs.cutpoint_resume_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.cutpoint_resume_decreases

/-- info: 'IxCC.Rt.Rc.Procs.cutpoint_tokens' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.cutpoint_tokens
