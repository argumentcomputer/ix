import Compilatrix.Cfg.Rc.Proof.Physical.PublicationFrames

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.partition_intervals' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.partition_intervals

/-- info: 'Compilatrix.Cfg.Rc.Native.publication_old_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.publication_old_live

/-- info: 'Compilatrix.Cfg.Rc.Native.publication_slot_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.publication_slot_frame
