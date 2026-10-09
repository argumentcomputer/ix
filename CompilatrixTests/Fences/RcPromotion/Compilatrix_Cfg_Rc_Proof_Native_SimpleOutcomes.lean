import Compilatrix.Cfg.Rc.Proof.Native.SimpleOutcomes

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.physical_declare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.physical_declare

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.physical_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.physical_return

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.physical_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.physical_trap
