import Compilatrix.Cfg.Rc.Proof.Native.Activation

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Activation.declare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Activation.declare

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Activation.lexical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Activation.lexical
