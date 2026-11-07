import IxCC.Rt.Rc.Proof.ReserveChains

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.FreeChain.frame_words' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.FreeChain.frame_words

/-- info: 'IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.ReleaseInvariant.reserve_chains
