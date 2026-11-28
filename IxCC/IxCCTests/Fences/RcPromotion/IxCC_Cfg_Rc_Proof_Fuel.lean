import IxCC.Cfg.Rc.Proof.Fuel

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.potential_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.potential_next

/-- info: 'IxCC.Cfg.Rc.potential_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.potential_step

/-- info: 'IxCC.Cfg.Rc.runs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.runs_run

/-- info: 'IxCC.Cfg.Rc.step_next_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.step_next_cases
