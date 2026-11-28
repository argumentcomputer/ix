import IxCC.Cfg.Rc.Proof.Native.EntryCursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ConsumedCursor.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ConsumedCursor.enter

/-- info: 'IxCC.Cfg.Rc.Native.Spec.Cursor.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.Cursor.enter
