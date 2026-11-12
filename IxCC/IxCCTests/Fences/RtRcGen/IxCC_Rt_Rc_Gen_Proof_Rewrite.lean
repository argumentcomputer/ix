import IxCC.Rt.Rc.Gen.Proof.Rewrite

/-! Exact axiom inventory of the general-layout heap: in-place reuse. -/

/-- info: 'IxCC.Rt.Rc.Gen.write_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.write_readable

/-- info: 'IxCC.Rt.Rc.Gen.write_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.write_writable

/-- info: 'IxCC.Rt.Rc.Gen.writeFields_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeFields_cons

/-- info: 'IxCC.Rt.Rc.Gen.writeFields_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeFields_perm

/-- info: 'IxCC.Rt.Rc.Gen.writeFields_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeFields_bytes

/-- info: 'IxCC.Rt.Rc.Gen.writeFields_wordAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeFields_wordAt

/-- info: 'IxCC.Rt.Rc.Gen.mem_zipIdx_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.mem_zipIdx_bounds

/-- info: 'IxCC.Rt.Rc.Gen.writeFields_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeFields_field

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_readable

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_writable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_writable

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_bytes_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_bytes_out

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_objectFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_objectFrame

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_wordAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_wordAt

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_protected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_protected

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_header

/-- info: 'IxCC.Rt.Rc.Gen.writeCell_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.writeCell_field

/-- info: 'IxCC.Rt.Rc.Gen.wordAt_read32_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.wordAt_read32_low

/-- info: 'IxCC.Rt.Rc.Gen.wordAt_read32_high_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.wordAt_read32_high_zero

/-- info: 'IxCC.Rt.Rc.Gen.dynamicHeader_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.dynamicHeader_reads

/-- info: 'IxCC.Rt.Rc.Gen.valueWord_remap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.valueWord_remap

/-- info: 'IxCC.Rt.Rc.Gen.fieldWord_remap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.fieldWord_remap

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.remap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.remap

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.rewrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.rewrite
