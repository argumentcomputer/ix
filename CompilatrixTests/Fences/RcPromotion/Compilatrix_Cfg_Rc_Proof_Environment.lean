import Compilatrix.Cfg.Rc.Proof.Environment

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.evalAction_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.evalAction_sub

/-- info: 'Compilatrix.Cfg.Rc.evalActions_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.evalActions_sub

/-- info: 'Compilatrix.Cfg.Rc.prefix_reach_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.prefix_reach_sub
