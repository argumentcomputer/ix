import CompilatrixTests.Aiur.WireProofs

/-! Exact wire proof cones. Only addressed wrappers inherit the existing
native BLAKE3 exception; codec and component facts use ordinary logic. -/

/-- info: 'Compilatrix.Ixon.u64OfLEBytes_eight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.u64OfLEBytes_eight

/-- info: 'Compilatrix.Aiur.Wire.fieldWord_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.fieldWord_roundtrip

/-- info: 'Compilatrix.Aiur.Wire.getField_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getField_spec

/-- info: 'Compilatrix.Aiur.Wire.getOption_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getOption_spec

/-- info: 'Compilatrix.Aiur.Wire.getNatArray_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getNatArray_spec

/-- info: 'Compilatrix.Aiur.Wire.getOp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getOp_spec

/-- info: 'Compilatrix.Aiur.Wire.ctrlBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.ctrlBytes_eq

/-- info: 'Compilatrix.Aiur.Wire.getCase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getCase_spec

/-- info: 'Compilatrix.Aiur.Wire.getCtrl_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getCtrl_spec

/-- info: 'Compilatrix.Aiur.Wire.getBlock_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getBlock_spec

/-- info: 'Compilatrix.Aiur.Wire.getLayout_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getLayout_spec

/-- info: 'Compilatrix.Aiur.Wire.getFunction_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getFunction_spec

/-- info: 'Compilatrix.Aiur.Wire.getCircuit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getCircuit_spec

/-- info: 'Compilatrix.Aiur.Wire.getComponent_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getComponent_spec

/-- info: 'Compilatrix.Aiur.Wire.getToplevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getToplevel_spec

/-- info: 'Compilatrix.Aiur.Wire.getPreimage_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.getPreimage_spec

/-- info: 'Compilatrix.Aiur.Wire.decode_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.decode_roundtrip

/-- info: 'Compilatrix.Aiur.Wire.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.decode_canonical

/-- info: 'Compilatrix.Aiur.Wire.decode_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.decode_fits

/-- info: 'Compilatrix.Aiur.Wire.preimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.preimage_injective

/-- info: 'Compilatrix.Aiur.Wire.Encoded.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.Encoded.roundtrip

/-- info: 'Compilatrix.Aiur.Wire.Addressed.canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.Addressed.canonical

/-- info: 'Compilatrix.Aiur.Wire.Addressed.fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.Addressed.fits

/-- info: 'Compilatrix.Aiur.Wire.Addressed.root_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.Addressed.root_eq

/-- info: 'Compilatrix.Aiur.Wire.Addressed.matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.Addressed.matches

/-- info: 'Compilatrix.Aiur.Wire.checkComponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.checkComponents

/-- info: 'Compilatrix.Aiur.Wire.ComponentChecked.evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.ComponentChecked.evidence

/-- info: 'Compilatrix.Aiur.Wire.Ingress.validated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Aiur.Wire.Ingress.validated

/-- info: 'CompilatrixTests.Aiur.WireProofs.counter_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.WireProofs.counter_fits

/-- info: 'CompilatrixTests.Aiur.WireProofs.counter_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.WireProofs.counter_roundtrip

/-- info: 'CompilatrixTests.Aiur.WireProofs.counter_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.WireProofs.counter_components

/-- info: 'CompilatrixTests.Aiur.WireProofs.ranked_mutual_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.WireProofs.ranked_mutual_components

/-- info: 'CompilatrixTests.Aiur.WireProofs.unranked_mutual_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CompilatrixTests.Aiur.WireProofs.unranked_mutual_rejected
