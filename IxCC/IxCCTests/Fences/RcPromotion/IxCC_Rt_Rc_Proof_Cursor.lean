import IxCC.Rt.Rc.Proof.Cursor

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.PendingCursor.next_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.PendingCursor.next_child

/-- info: 'IxCC.Rt.Rc.Procs.PendingParent.cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.PendingParent.cursor

/-- info: 'IxCC.Rt.Rc.Procs.cursor_field_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.cursor_field_address

/-- info: 'IxCC.Rt.Rc.Procs.small_word_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.small_word_sub
