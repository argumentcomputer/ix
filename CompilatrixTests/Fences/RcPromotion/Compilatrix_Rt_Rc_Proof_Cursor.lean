import Compilatrix.Rt.Rc.Proof.Cursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Rt.Rc.Procs.PendingCursor.next_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.PendingCursor.next_child

/-- info: 'Compilatrix.Rt.Rc.Procs.PendingParent.cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.PendingParent.cursor

/-- info: 'Compilatrix.Rt.Rc.Procs.cursor_field_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.cursor_field_address

/-- info: 'Compilatrix.Rt.Rc.Procs.small_word_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Rt.Rc.Procs.small_word_sub
