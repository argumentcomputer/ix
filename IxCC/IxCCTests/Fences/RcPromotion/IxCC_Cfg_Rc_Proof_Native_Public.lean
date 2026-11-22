import IxCC.Cfg.Rc.Proof.Native.Public

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Public.Spec.accepted_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.accepted_drop

/-- info: 'IxCC.Cfg.Rc.Public.Spec.assemble_drop' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.assemble_drop

/-- info: 'IxCC.Cfg.Rc.Public.Spec.assemble_existing' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.assemble_existing

/-- info: 'IxCC.Cfg.Rc.Public.Spec.lower_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.lower_parts
