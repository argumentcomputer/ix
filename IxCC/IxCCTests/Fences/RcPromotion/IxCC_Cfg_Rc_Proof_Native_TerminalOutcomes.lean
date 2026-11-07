import IxCC.Cfg.Rc.Proof.Native.TerminalOutcomes

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Activation.return_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Activation.return_result

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Activation.trap_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Activation.trap_result
