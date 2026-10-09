import Compilatrix.Cfg.Rc.Proof.Physical.PublicInit

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.accepted_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.accepted_init

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.cxInit_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.cxInit_split

/-- info: 'Compilatrix.Cfg.Rc.Public.Spec.initialize_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.Spec.initialize_heap
