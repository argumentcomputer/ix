import IxCC.Cfg.Rc.Proof.Physical.PublicEval

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.accepted_eval_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.accepted_eval_stages

/-- info: 'IxCC.Cfg.Rc.Native.Spec.eval_transfer_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.eval_transfer_sim

/-- info: 'IxCC.Cfg.Rc.Native.Spec.program_eval_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.program_eval_transfer
