import IxCC.Cfg.Rc.Proof.Physical.Bridge.ReadyTokens

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.Tokens.activate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.Tokens.activate

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.canDup_live' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.canDup_live

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.increment_ready_tokens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.increment_ready_tokens
