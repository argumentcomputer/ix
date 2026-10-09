import Compilatrix.Cfg.Rc.Proof.Native.TerminalOutcomes

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Activation.return_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Activation.return_result

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Activation.trap_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Activation.trap_result
