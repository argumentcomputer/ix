import Compilatrix.Cfg.Rc.Proof.Native.TrapCursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.ConsumedCursor.trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.ConsumedCursor.trap

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Cursor.trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Cursor.trap
