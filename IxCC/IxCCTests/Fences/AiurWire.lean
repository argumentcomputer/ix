import IxCCTests.Aiur.WireProofs

/-! Exact wire proof cones, on ordinary logic (the addressed wrappers' hash is pure BLAKE3). -/

/-- info: 'IxCC.Ixon.u64OfLEBytes_eight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.u64OfLEBytes_eight

/-- info: 'IxCC.Aiur.Wire.fieldWord_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.fieldWord_roundtrip

/-- info: 'IxCC.Aiur.Wire.getField_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getField_spec

/-- info: 'IxCC.Aiur.Wire.getOption_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getOption_spec

/-- info: 'IxCC.Aiur.Wire.getNatArray_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getNatArray_spec

/-- info: 'IxCC.Aiur.Wire.getOp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getOp_spec

/-- info: 'IxCC.Aiur.Wire.ctrlBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.ctrlBytes_eq

/-- info: 'IxCC.Aiur.Wire.getCase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getCase_spec

/-- info: 'IxCC.Aiur.Wire.getCtrl_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getCtrl_spec

/-- info: 'IxCC.Aiur.Wire.getBlock_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getBlock_spec

/-- info: 'IxCC.Aiur.Wire.getLayout_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getLayout_spec

/-- info: 'IxCC.Aiur.Wire.getFunction_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getFunction_spec

/-- info: 'IxCC.Aiur.Wire.getCircuit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getCircuit_spec

/-- info: 'IxCC.Aiur.Wire.getComponent_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getComponent_spec

/-- info: 'IxCC.Aiur.Wire.getToplevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getToplevel_spec

/-- info: 'IxCC.Aiur.Wire.getPreimage_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.getPreimage_spec

/-- info: 'IxCC.Aiur.Wire.decode_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.decode_roundtrip

/-- info: 'IxCC.Aiur.Wire.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.decode_canonical

/-- info: 'IxCC.Aiur.Wire.decode_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.decode_fits

/-- info: 'IxCC.Aiur.Wire.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.preimage_injective

/-- info: 'IxCC.Aiur.Wire.Encoded.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.Encoded.roundtrip

/-- info: 'IxCC.Aiur.Wire.Addressed.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.Addressed.canonical

/-- info: 'IxCC.Aiur.Wire.Addressed.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.Addressed.fits

/-- info: 'IxCC.Aiur.Wire.Addressed.root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.Addressed.root_eq

/-- info: 'IxCC.Aiur.Wire.Addressed.matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.Addressed.matches

/-- info: 'IxCC.Aiur.Wire.checkComponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.checkComponents

/-- info: 'IxCC.Aiur.Wire.ComponentChecked.evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.ComponentChecked.evidence

/-- info: 'IxCC.Aiur.Wire.Ingress.validated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Aiur.Wire.Ingress.validated

/-- info: 'IxCCTests.Aiur.WireProofs.counter_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.WireProofs.counter_fits

/-- info: 'IxCCTests.Aiur.WireProofs.counter_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.WireProofs.counter_roundtrip

/-- info: 'IxCCTests.Aiur.WireProofs.counter_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.WireProofs.counter_components

/-- info: 'IxCCTests.Aiur.WireProofs.ranked_mutual_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.WireProofs.ranked_mutual_components

/-- info: 'IxCCTests.Aiur.WireProofs.unranked_mutual_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCCTests.Aiur.WireProofs.unranked_mutual_rejected
