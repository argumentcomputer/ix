import IxCC.Rt.Rc.Proof.Memory

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.countAddress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.countAddress

/-- info: 'IxCC.Rt.Rc.Procs.storeCount_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.storeCount_bytes

/-- info: 'IxCC.Rt.Rc.Procs.storeCount_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.storeCount_frame

/-- info: 'IxCC.Rt.Rc.Procs.storeCount_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.storeCount_word
