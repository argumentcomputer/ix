import IxCC.Cfg.Rc.Proof.Native.Activation

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Activation.declare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Activation.declare

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Activation.lexical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Activation.lexical
