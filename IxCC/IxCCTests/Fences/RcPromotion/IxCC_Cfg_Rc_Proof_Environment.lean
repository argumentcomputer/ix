import IxCC.Cfg.Rc.Proof.Environment

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.evalAction_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.evalAction_sub

/-- info: 'IxCC.Cfg.Rc.evalActions_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.evalActions_sub

/-- info: 'IxCC.Cfg.Rc.prefix_reach_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.prefix_reach_sub
