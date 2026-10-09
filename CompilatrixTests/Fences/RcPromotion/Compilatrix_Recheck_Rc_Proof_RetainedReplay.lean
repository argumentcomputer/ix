import Compilatrix.Recheck.Rc.Proof.RetainedReplay

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Recheck.RcReplay.SourceWitness.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.SourceWitness.readback

/-- info: 'Compilatrix.Recheck.RcReplay.checked_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.checked_retained

/-- info: 'Compilatrix.Recheck.RcReplay.rejected_treeView' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.rejected_treeView

/-- info: 'Compilatrix.Recheck.RcReplay.source_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.source_retained

/-- info: 'Compilatrix.Recheck.RcReplay.source_retained_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.source_retained_success
