import Compilatrix.Cfg.Rc.Proof.Fuel

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.potential_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.potential_next

/-- info: 'Compilatrix.Cfg.Rc.potential_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.potential_step

/-- info: 'Compilatrix.Cfg.Rc.runs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.runs_run

/-- info: 'Compilatrix.Cfg.Rc.step_next_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.step_next_cases
