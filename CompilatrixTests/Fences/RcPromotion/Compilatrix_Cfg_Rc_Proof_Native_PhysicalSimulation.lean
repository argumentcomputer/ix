import Compilatrix.Cfg.Rc.Proof.Native.PhysicalSimulation

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.checked_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.checked_physical

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.eval_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.eval_physical

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.public_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.public_physical
