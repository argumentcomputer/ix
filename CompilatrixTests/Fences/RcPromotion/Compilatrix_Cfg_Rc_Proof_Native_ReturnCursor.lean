import Compilatrix.Cfg.Rc.Proof.Native.ReturnCursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.ConsumedCursor.ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.ConsumedCursor.ret

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Cursor.ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Cursor.ret
