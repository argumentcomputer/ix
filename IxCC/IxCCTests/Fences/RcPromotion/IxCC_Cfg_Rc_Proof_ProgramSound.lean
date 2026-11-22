import IxCC.Cfg.Rc.Proof.ProgramSound

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.checked_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checked_entry

/-- info: 'IxCC.Cfg.Rc.entries_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.entries_ok

/-- info: 'IxCC.Cfg.Rc.generate_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.generate_entry
