import Compilatrix.Recheck.Rc.Proof.Replay

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Recheck.RcReplay.runFront_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.runFront_spec

/-- info: 'Compilatrix.Recheck.RcReplay.source_refines_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.source_refines_cfg
