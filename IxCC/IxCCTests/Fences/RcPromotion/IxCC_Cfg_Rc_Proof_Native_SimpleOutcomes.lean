import IxCC.Cfg.Rc.Proof.Native.SimpleOutcomes

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_declare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_declare

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_return

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_trap
