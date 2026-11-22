import IxCC.Recheck.Rc.Proof.SourceSound

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Recheck.RcReplay.Front.diverges_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Front.diverges_of

/-- info: 'IxCC.Recheck.RcReplay.Front.safe_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Front.safe_of

/-- info: 'IxCC.Recheck.RcReplay.Front.sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Front.sound_of

/-- info: 'IxCC.Recheck.RcReplay.source_goesWrong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.source_goesWrong
