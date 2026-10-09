import Compilatrix.Cfg.Rc.Proof.Native.ReturnedObservation

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Returned.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Returned.finish

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Returned.observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Returned.observe
