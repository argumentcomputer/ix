import IxCC.Cfg.Rc.Proof.Extend

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.At.extend' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.At.extend

/-- info: 'IxCC.Cfg.Rc.EnvSub.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.EnvSub.trans

/-- info: 'IxCC.Cfg.Rc.Joins.extend' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Joins.extend
