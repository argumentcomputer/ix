import Compilatrix.Cfg.Rc.Proof.Physical.ReservedHeader

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Cfg.Rc.Native.unique_header_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.unique_header_reads

/-- info: 'Compilatrix.Cfg.Rc.Native.wordAt_read32_high_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.wordAt_read32_high_zero

/-- info: 'Compilatrix.Cfg.Rc.Native.wordAt_read32_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Rc.Native.wordAt_read32_low
