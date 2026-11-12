import IxCC.Rt.Rc.Gen.Proof.InPlace

/-! Exact axiom inventory of the general-layout heap: in-place reuse. -/

/-- info: 'IxCC.Rt.Rc.Gen.relabelSlot_address' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.relabelSlot_address

/-- info: 'IxCC.Rt.Rc.Gen.relabelSlot_cls' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.relabelSlot_cls

/-- info: 'IxCC.Rt.Rc.Gen.relabelSlot_kind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.relabelSlot_kind

/-- info: 'IxCC.Rt.Rc.Gen.relabelSlot_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.relabelSlot_free

/-- info: 'IxCC.Rt.Rc.Gen.ArenaPartition.separate' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ArenaPartition.separate

/-- info: 'IxCC.Rt.Rc.Gen.ArenaPartition.relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.ArenaPartition.relabel

/-- info: 'IxCC.Rt.Rc.Gen.freeChain_frame' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.freeChain_frame

/-- info: 'IxCC.Rt.Rc.Gen.balance_idle' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.balance_idle

/-- info: 'IxCC.Rt.Rc.Gen.live_of_dynCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.live_of_dynCount

/-- info: 'IxCC.Rt.Rc.Gen.inPlace_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.inPlace_ready
