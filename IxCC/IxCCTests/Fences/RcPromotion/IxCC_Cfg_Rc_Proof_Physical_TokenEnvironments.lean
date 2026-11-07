import IxCC.Cfg.Rc.Proof.Physical.TokenEnvironments

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Tokens.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Tokens.extend

/-- info: 'IxCC.Cfg.Rc.Native.Tokens.present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Tokens.present

/-- info: 'IxCC.Cfg.Rc.Native.Tokens.restrict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Tokens.restrict

/-- info: 'IxCC.Cfg.Rc.Native.copies_eval_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.copies_eval_sub

/-- info: 'IxCC.Cfg.Rc.Native.copies_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.copies_variables

/-- info: 'IxCC.Cfg.Rc.Native.drops_eval_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.drops_eval_sub

/-- info: 'IxCC.Cfg.Rc.Native.drops_variables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.drops_variables

/-- info: 'IxCC.Cfg.Rc.Native.envBounded_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.envBounded_sub

/-- info: 'IxCC.Cfg.Rc.Native.env_absent_sub' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.env_absent_sub

/-- info: 'IxCC.Cfg.Rc.Native.env_agree_live' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.env_agree_live

/-- info: 'IxCC.Cfg.Rc.Native.evalActions_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.evalActions_agree

/-- info: 'IxCC.Cfg.Rc.Native.transfer_eval_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.transfer_eval_sub
