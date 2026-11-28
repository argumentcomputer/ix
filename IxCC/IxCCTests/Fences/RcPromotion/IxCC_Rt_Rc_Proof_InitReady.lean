import IxCC.Rt.Rc.Proof.InitReady

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.Init.cxInit_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Init.cxInit_ready

/-- info: 'IxCC.Rt.Rc.Procs.Init.empty_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Init.empty_ready
