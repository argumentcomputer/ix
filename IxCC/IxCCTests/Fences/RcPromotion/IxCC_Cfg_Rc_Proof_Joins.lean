import IxCC.Cfg.Rc.Proof.Joins

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Joins.agree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Joins.agree

/-- info: 'IxCC.Cfg.Rc.Joins.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Joins.lookup

/-- info: 'IxCC.Cfg.Rc.Joins.mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Joins.mono
