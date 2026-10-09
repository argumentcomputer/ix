import Compilatrix.Cfg.Rc.Proof.Native.EntryCursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.ConsumedCursor.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.ConsumedCursor.enter

/-- info: 'Compilatrix.Cfg.Rc.Native.Spec.Cursor.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.Spec.Cursor.enter
