import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorInvariant

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Proof.CtorOk.scanned' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.CtorOk.scanned

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.alloc

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.changeCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.changeCount

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.dropAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.dropAll

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.free' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.free

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.releaseOne' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.releaseOne

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.sameBodies' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.HeapCtorOk.sameBodies

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.heapCtorOk_empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.heapCtorOk_empty
