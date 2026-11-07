import IxCC.Rt.Rc.Proof.Readback.Fuel

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.Readback.liveAt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.liveAt_iff

/-- info: 'IxCC.Rt.Rc.Procs.Readback.liveBefore_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.liveBefore_mono

/-- info: 'IxCC.Rt.Rc.Procs.Readback.liveBefore_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.liveBefore_step

/-- info: 'IxCC.Rt.Rc.Procs.Readback.liveBefore_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.liveBefore_strict

/-- info: 'IxCC.Rt.Rc.Procs.Readback.liveLocations_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.liveLocations_nodup

/-- info: 'IxCC.Rt.Rc.Procs.Readback.toFirList_of_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.toFirList_of_each

/-- info: 'IxCC.Rt.Rc.Procs.Readback.toFir_liveFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.toFir_liveFuel

/-- info: 'IxCC.Rt.Rc.Procs.Readback.toFir_totalLive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.toFir_totalLive
