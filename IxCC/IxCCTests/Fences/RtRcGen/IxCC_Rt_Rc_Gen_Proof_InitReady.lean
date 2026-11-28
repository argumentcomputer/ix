import IxCC.Rt.Rc.Gen.Proof.InitReady

/-! Exact axiom inventory of the general-layout heap. -/

/-- info: 'IxCC.Rt.Rc.Gen.Init.cxInit_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.Init.cxInit_ready

/-- info: 'IxCC.Rt.Rc.Gen.Init.empty_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Gen.Init.empty_ready
