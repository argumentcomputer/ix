import IxCC.Cfg.Rc.Proof.Scoped

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.checkScopedProgram_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checkScopedProgram_parts

/-- info: 'IxCC.Cfg.Rc.checked_names' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checked_names

/-- info: 'IxCC.Cfg.Rc.checked_source_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checked_source_dense

/-- info: 'IxCC.Cfg.Rc.programNames_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.programNames_lookup
