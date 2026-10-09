import Compilatrix.Recheck.Rc.Proof.SourceSound

/-! Exact accepted RC axiom inventory. -/

/-- info: 'Compilatrix.Recheck.RcReplay.Front.diverges_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.Front.diverges_of

/-- info: 'Compilatrix.Recheck.RcReplay.Front.safe_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.Front.safe_of

/-- info: 'Compilatrix.Recheck.RcReplay.Front.sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.Front.sound_of

/-- info: 'Compilatrix.Recheck.RcReplay.source_goesWrong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Recheck.RcReplay.source_goesWrong
