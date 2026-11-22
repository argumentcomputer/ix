import IxCC.Cfg.Rc.Proof.Physical.PublicationFrames

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.partition_intervals' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.partition_intervals

/-- info: 'IxCC.Cfg.Rc.Native.publication_old_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publication_old_live

/-- info: 'IxCC.Cfg.Rc.Native.publication_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.publication_slot_frame
