import IxCC.Recheck.Rc.Proof.Replay

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Recheck.RcReplay.runFront_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.runFront_spec

/-- info: 'IxCC.Recheck.RcReplay.source_refines_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.source_refines_cfg
