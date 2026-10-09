import Compilatrix.Cfg.Rc.Proof.Native.CallEntry

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.consume_user_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.consume_user_call

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.consumed_user_call_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.consumed_user_call_entry
