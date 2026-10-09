import Compilatrix.Cfg.Rc.Proof.Language

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.checked_lower_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checked_lower_refines

/-- info: 'Compilatrix.Cfg.Rc.checked_refines_lang' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checked_refines_lang

/-- info: 'Compilatrix.Cfg.Rc.generate_exports' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.generate_exports

/-- info: 'Compilatrix.Cfg.Rc.lowerFunction_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.lowerFunction_params

/-- info: 'Compilatrix.Cfg.Rc.run_clockMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.run_clockMono
