import Compilatrix.Cfg.Rc.Proof.Coverage

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.collect_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.collect_member

/-- info: 'Compilatrix.Cfg.Rc.collect_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.collect_tail

/-- info: 'Compilatrix.Cfg.Rc.step_checked_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.step_checked_member
