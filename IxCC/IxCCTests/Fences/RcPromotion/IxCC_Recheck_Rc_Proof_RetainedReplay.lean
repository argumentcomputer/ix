import IxCC.Recheck.Rc.Proof.RetainedReplay

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Recheck.RcReplay.SourceWitness.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.SourceWitness.readback

/-- info: 'IxCC.Recheck.RcReplay.checked_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.checked_retained

/-- info: 'IxCC.Recheck.RcReplay.rejected_treeView' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.rejected_treeView

/-- info: 'IxCC.Recheck.RcReplay.source_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.source_retained

/-- info: 'IxCC.Recheck.RcReplay.source_retained_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.source_retained_success
