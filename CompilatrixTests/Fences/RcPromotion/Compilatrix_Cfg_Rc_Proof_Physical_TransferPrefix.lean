import Compilatrix.Cfg.Rc.Proof.Physical.TransferPrefix

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.encodePrefix_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.encodePrefix_append

/-- info: 'Compilatrix.Cfg.Rc.Native.transfer_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.transfer_prefix
