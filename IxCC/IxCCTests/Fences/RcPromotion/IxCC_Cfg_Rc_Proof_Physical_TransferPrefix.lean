import IxCC.Cfg.Rc.Proof.Physical.TransferPrefix

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.encodePrefix_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.encodePrefix_append

/-- info: 'IxCC.Cfg.Rc.Native.transfer_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.transfer_prefix
