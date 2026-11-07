import IxCC.Cfg.Rc.Proof.Native.PhysicalSimulation

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.checked_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.checked_physical

/-- info: 'IxCC.Cfg.Rc.Native.Spec.eval_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.eval_physical

/-- info: 'IxCC.Cfg.Rc.Native.Spec.public_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.public_physical
