import IxCC.Rt.Rc.Gen.Proof.LiveMemory

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.bytes

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.count_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.count_encoding

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.count_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.count_load

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.count_readable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.count_readable

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.count_writable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.count_writable

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.nobj_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.nobj_le

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.scalar_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.scalar_values

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.scanned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.scanned

/-- info: 'IxCC.Rt.Rc.Gen.LiveCell.tag_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.LiveCell.tag_le

/-- info: 'IxCC.Rt.Rc.Gen.cellBytesOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.cellBytesOf_le

/-- info: 'IxCC.Rt.Rc.Gen.classOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.classOf_lt

/-- info: 'IxCC.Rt.Rc.Gen.classOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.classOf_spec

/-- info: 'IxCC.Rt.Rc.Gen.layoutOf_bounds' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.layoutOf_bounds

/-- info: 'IxCC.Rt.Rc.Gen.layoutOf_cls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.layoutOf_cls

/-- info: 'IxCC.Rt.Rc.Gen.le_classWords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.le_classWords

/-- info: 'IxCC.Rt.Rc.Gen.scalarWord_lit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.scalarWord_lit

/-- info: 'IxCC.Rt.Rc.Procs.HeapLive.toGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.HeapLive.toGen

/-- info: 'IxCC.Rt.Rc.Procs.LiveCell.toGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.LiveCell.toGen
