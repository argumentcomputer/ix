import Compilatrix.Cfg.Rc.Proof.Scoped

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.checkScopedProgram_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checkScopedProgram_parts

/-- info: 'Compilatrix.Cfg.Rc.checked_names' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checked_names

/-- info: 'Compilatrix.Cfg.Rc.checked_source_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checked_source_dense

/-- info: 'Compilatrix.Cfg.Rc.programNames_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.programNames_lookup
