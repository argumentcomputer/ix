import IxCC.Cfg.Rc.Proof.Physical.PublicInit

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Public.Spec.accepted_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.accepted_init

/-- info: 'IxCC.Cfg.Rc.Public.Spec.cxInit_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.cxInit_split

/-- info: 'IxCC.Cfg.Rc.Public.Spec.initialize_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.initialize_heap
