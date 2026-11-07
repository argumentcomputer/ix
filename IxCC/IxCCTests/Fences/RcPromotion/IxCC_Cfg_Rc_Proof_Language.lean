import IxCC.Cfg.Rc.Proof.Language

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.checked_lower_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checked_lower_refines

/-- info: 'IxCC.Cfg.Rc.checked_refines_lang' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checked_refines_lang

/-- info: 'IxCC.Cfg.Rc.generate_exports' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.generate_exports

/-- info: 'IxCC.Cfg.Rc.lowerFunction_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.lowerFunction_params

/-- info: 'IxCC.Cfg.Rc.run_clockMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.run_clockMono
