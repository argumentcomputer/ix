import Compilatrix.Cfg.Rc.Proof.Physical.PublicEval

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.accepted_eval_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.accepted_eval_stages

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.eval_transfer_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.eval_transfer_sim

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.program_eval_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.program_eval_transfer
