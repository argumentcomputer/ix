import IxCC.Cfg.Rc.Proof.Physical.ResultEval

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ResultAt.eval_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ResultAt.eval_forward

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ResultAt.eval_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ResultAt.eval_timeout

/-- info: 'IxCC.Cfg.Rc.Native.Spec.resultAt_eval_sim_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.resultAt_eval_sim_succ
