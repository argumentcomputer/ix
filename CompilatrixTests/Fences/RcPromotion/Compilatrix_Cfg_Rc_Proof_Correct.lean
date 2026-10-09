import Compilatrix.Cfg.Rc.Proof.Correct

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.checked_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checked_correct

/-- info: 'Compilatrix.Cfg.Rc.checked_correct_traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.checked_correct_traced

/-- info: 'Compilatrix.Cfg.Rc.step_ret_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.step_ret_nil
