import IxCC.Cfg.Rc.Proof.Physical.SlotPromotion

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.partition_address_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.partition_address_unique

/-- info: 'IxCC.Cfg.Rc.Native.partition_publish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.partition_publish

/-- info: 'IxCC.Cfg.Rc.Native.publishSlot_address' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publishSlot_address

/-- info: 'IxCC.Cfg.Rc.Native.publishSlot_class' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publishSlot_class

/-- info: 'IxCC.Cfg.Rc.Native.publishSlots_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publishSlots_get
