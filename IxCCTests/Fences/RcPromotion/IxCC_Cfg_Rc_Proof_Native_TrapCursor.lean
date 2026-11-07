import IxCC.Cfg.Rc.Proof.Native.TrapCursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ConsumedCursor.trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ConsumedCursor.trap

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Cursor.trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Cursor.trap
