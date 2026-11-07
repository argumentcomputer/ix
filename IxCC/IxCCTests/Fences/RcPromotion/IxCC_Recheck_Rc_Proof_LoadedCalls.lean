import IxCC.Recheck.Rc.Proof.LoadedCalls

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Recheck.RcReplay.erased_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.erased_view

/-- info: 'IxCC.Recheck.RcReplay.loaded_call_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.loaded_call_sim
