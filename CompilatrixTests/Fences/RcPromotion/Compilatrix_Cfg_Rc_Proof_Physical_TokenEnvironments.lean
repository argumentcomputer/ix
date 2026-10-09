import Compilatrix.Cfg.Rc.Proof.Physical.TokenEnvironments

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Tokens.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Tokens.extend

/-- info: 'Compilatrix.Cfg.Rc.Native.Tokens.present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Tokens.present

/-- info: 'Compilatrix.Cfg.Rc.Native.Tokens.restrict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Tokens.restrict

/-- info: 'Compilatrix.Cfg.Rc.Native.copies_eval_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.copies_eval_sub

/-- info: 'Compilatrix.Cfg.Rc.Native.copies_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.copies_variables

/-- info: 'Compilatrix.Cfg.Rc.Native.drops_eval_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.drops_eval_sub

/-- info: 'Compilatrix.Cfg.Rc.Native.drops_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.drops_variables

/-- info: 'Compilatrix.Cfg.Rc.Native.envBounded_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.envBounded_sub

/-- info: 'Compilatrix.Cfg.Rc.Native.env_absent_sub' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.env_absent_sub

/-- info: 'Compilatrix.Cfg.Rc.Native.env_agree_live' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.env_agree_live

/-- info: 'Compilatrix.Cfg.Rc.Native.evalActions_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.evalActions_agree

/-- info: 'Compilatrix.Cfg.Rc.Native.transfer_eval_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.transfer_eval_sub
