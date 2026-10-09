import Compilatrix.Cfg.Rc.Proof.Physical.ResultEval

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.ResultAt.eval_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.ResultAt.eval_forward

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.ResultAt.eval_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.ResultAt.eval_timeout

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.resultAt_eval_sim_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.resultAt_eval_sim_succ
