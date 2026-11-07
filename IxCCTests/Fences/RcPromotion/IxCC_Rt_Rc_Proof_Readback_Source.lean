import IxCC.Rt.Rc.Proof.Readback.Source

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Rt.Rc.Procs.Readback.SourceForest.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.SourceForest.get

/-- info: 'IxCC.Rt.Rc.Procs.Readback.SourceForest.length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.SourceForest.length

/-- info: 'IxCC.Rt.Rc.Procs.Readback.SourceForest.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.SourceForest.observations

/-- info: 'IxCC.Rt.Rc.Procs.Readback.SourceTree.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.SourceTree.observations

/-- info: 'IxCC.Rt.Rc.Procs.Readback.source_readback_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.source_readback_region

/-- info: 'IxCC.Rt.Rc.Procs.Readback.toFirList_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.toFirList_rel

/-- info: 'IxCC.Rt.Rc.Procs.Readback.typed_of_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Procs.Readback.typed_of_tree
