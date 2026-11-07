import IxCC.Cfg.Rc.Proof.Physical.PublicationTokens

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.idle_field_tokens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.idle_field_tokens

/-- info: 'IxCC.Cfg.Rc.Native.publication_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publication_balance

/-- info: 'IxCC.Cfg.Rc.Native.publication_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publication_children
