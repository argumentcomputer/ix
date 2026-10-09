import Compilatrix.Cfg.Rc.Proof.Physical.TailResult

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.source_call_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.source_call_arity

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.tail_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.tail_result
