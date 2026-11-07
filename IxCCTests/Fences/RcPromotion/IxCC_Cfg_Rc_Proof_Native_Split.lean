import IxCC.Cfg.Rc.Proof.Native.Split

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Public.Spec.accepted_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.accepted_split

/-- info: 'IxCC.Cfg.Rc.Public.Spec.assemble_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.assemble_split

/-- info: 'IxCC.Cfg.Rc.Public.Spec.drop_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.drop_split

/-- info: 'IxCC.Cfg.Rc.Public.Spec.program_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.program_split
