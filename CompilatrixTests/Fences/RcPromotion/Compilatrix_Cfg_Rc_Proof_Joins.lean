import Compilatrix.Cfg.Rc.Proof.Joins

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Joins.agree' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Joins.agree

/-- info: 'Compilatrix.Cfg.Rc.Joins.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Joins.lookup

/-- info: 'Compilatrix.Cfg.Rc.Joins.mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Joins.mono
