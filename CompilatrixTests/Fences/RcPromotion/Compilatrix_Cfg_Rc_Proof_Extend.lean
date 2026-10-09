import Compilatrix.Cfg.Rc.Proof.Extend

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.At.extend' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.At.extend

/-- info: 'Compilatrix.Cfg.Rc.EnvSub.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.EnvSub.trans

/-- info: 'Compilatrix.Cfg.Rc.Joins.extend' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Joins.extend
