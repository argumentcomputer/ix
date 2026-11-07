import IxCC.Cfg.Rc.Proof.Native.CallEntry

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.consume_user_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.consume_user_call

/-- info: 'IxCC.Cfg.Rc.Native.Spec.consumed_user_call_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.consumed_user_call_entry
