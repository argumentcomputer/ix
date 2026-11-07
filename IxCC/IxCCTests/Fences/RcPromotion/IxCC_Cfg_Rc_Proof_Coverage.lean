import IxCC.Cfg.Rc.Proof.Coverage

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.collect_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.collect_member

/-- info: 'IxCC.Cfg.Rc.collect_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.collect_tail

/-- info: 'IxCC.Cfg.Rc.step_checked_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.step_checked_member
