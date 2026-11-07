import IxCC.Cfg.Rc.Proof.Physical.TailResult

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.source_call_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.source_call_arity

/-- info: 'IxCC.Cfg.Rc.Native.Spec.tail_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.tail_result
