import IxCC.Cfg.Rc.Proof.Physical.DropTokens

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Tokens.hold_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Tokens.hold_head

/-- info: 'IxCC.Cfg.Rc.Native.Tokens.restore_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Tokens.restore_head
