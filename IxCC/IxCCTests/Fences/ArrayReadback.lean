import IxCC.Rt.Readback.Array

/-! Exact axiom fences for `IxCC.Rt.Readback.Array` (`ByteArray`, UTF-8
`String`, `LimbArray`, `BigNat` threshold + canonical limb cells, and boxed
`Array` readback across both live dynamic heap cells and immortal `.rodata`
cells). Every theorem depends strictly on subsets of
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'IxCC.Rt.Readback.readbackByteArray_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackByteArray_live

/-- info: 'IxCC.Rt.Readback.readbackByteArray_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackByteArray_static

/-- info: 'IxCC.Rt.Readback.readbackByteArrayObs_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackByteArrayObs_live

/-- info: 'IxCC.Rt.Readback.readbackByteArrayObs_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackByteArrayObs_static

/-- info: 'IxCC.Rt.Readback.readbackString_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackString_live

/-- info: 'IxCC.Rt.Readback.readbackString_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackString_static

/-- info: 'IxCC.Rt.Readback.readbackLimbArray_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackLimbArray_live

/-- info: 'IxCC.Rt.Readback.readbackLimbArray_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackLimbArray_static

/-- info: 'IxCC.Rt.Readback.isCanonicalBigNat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.isCanonicalBigNat_iff

/-- info: 'IxCC.Rt.Readback.readbackBigNat_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackBigNat_small

/-- info: 'IxCC.Rt.Readback.readbackBigNat_big_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackBigNat_big_live

/-- info: 'IxCC.Rt.Readback.readbackBigNat_big_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackBigNat_big_static

/-- info: 'IxCC.Rt.Readback.readbackBigNat_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackBigNat_threshold

/-- info: 'IxCC.Rt.Readback.readbackBoxedArray_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackBoxedArray_live

/-- info: 'IxCC.Rt.Readback.readbackBoxedArray_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Readback.readbackBoxedArray_static
