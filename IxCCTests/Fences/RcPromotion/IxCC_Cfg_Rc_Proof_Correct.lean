import IxCC.Cfg.Rc.Proof.Correct

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.checked_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checked_correct

/-- info: 'IxCC.Cfg.Rc.checked_correct_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checked_correct_traced

/-- info: 'IxCC.Cfg.Rc.step_ret_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.step_ret_nil
