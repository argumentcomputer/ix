import Compilatrix.Cfg.Rc.Proof.PublicApi

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Public.dropWrapper_block' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.dropWrapper_block

/-- info: 'Compilatrix.Cfg.Rc.Public.reps_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Public.reps_drop
