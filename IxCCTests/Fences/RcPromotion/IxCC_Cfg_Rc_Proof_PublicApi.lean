import IxCC.Cfg.Rc.Proof.PublicApi

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Public.dropWrapper_block' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.dropWrapper_block

/-- info: 'IxCC.Cfg.Rc.Public.reps_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.reps_drop
