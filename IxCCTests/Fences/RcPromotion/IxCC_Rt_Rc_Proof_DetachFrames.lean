import IxCC.Rt.Rc.Proof.DetachFrames

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.CursorChain.free_cell' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.CursorChain.free_cell

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.detach_cursor_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.detach_cursor_frame

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.detach_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.detach_slot_frame
