import IxCC.Rt.Rc.Proof.LoopControl

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.recycle_rank_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.recycle_rank_decreases

/-- info: 'IxCC.Rt.Rc.Procs.recycle_tokens' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.recycle_tokens

/-- info: 'IxCC.Rt.Rc.Procs.release_rank_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.release_rank_decreases

/-- info: 'IxCC.Rt.Rc.Procs.resume_rank_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.resume_rank_decreases

/-- info: 'IxCC.Rt.Rc.Procs.resume_tokens' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.resume_tokens
