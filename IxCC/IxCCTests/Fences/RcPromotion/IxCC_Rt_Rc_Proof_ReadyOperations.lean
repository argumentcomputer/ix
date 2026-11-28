import IxCC.Rt.Rc.Proof.ReadyOperations

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.increment_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.increment_ready

/-- info: 'IxCC.Rt.Rc.Procs.AllocatorReady.release_caller_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.AllocatorReady.release_caller_ready
