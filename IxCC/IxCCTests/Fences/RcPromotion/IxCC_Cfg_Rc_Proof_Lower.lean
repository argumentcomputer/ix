import IxCC.Cfg.Rc.Proof.Lower

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.checkFunction_intercepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checkFunction_intercepts

/-- info: 'IxCC.Cfg.Rc.lower_actionPrefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.lower_actionPrefix

/-- info: 'IxCC.Cfg.Rc.markerRhs_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.markerRhs_eq

/-- info: 'IxCC.Cfg.Rc.skeleton_action' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.skeleton_action
