import Compilatrix.Cfg.Rc.Proof.ProgramSound

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.checked_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checked_entry

/-- info: 'Compilatrix.Cfg.Rc.entries_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.entries_ok

/-- info: 'Compilatrix.Cfg.Rc.generate_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.generate_entry
