import IxCC.BigNat.Proof.Entry
import IxCC.BigNat.Bootstrap
import IxCC.Rt.BigNat.Cell
import IxCC.Rt.BigNat.ProofProcs
import IxCC.Rt.BigNat.Proof

/-! Exact axiom fences for Wave 3 Phase 4 arbitrary-precision `Nat` slow-path
entrypoints (`IxCC.BigNat.Proof.Entry`), `LimbOps` word equations
(`IxCC.BigNat.Bootstrap`), unified `NatVal` / `.rodata` representation
(`IxCC.Rt.BigNat.Cell`), and zero-`natOverflow` LIR simulation proofs
(`IxCC.Rt.BigNat.ProofProcs`, `IxCC.Rt.BigNat.Proof`).

Every theorem depends strictly on subsets of `[propext, Classical.choice, Quot.sound]`. -/

/-! ## `IxCC.BigNat.Entry` Layer-1 Correctness & Normal-Form Fences -/

/-- info: 'IxCC.BigNat.Entry.canonical_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_ofNat

/-- info: 'IxCC.BigNat.Entry.val_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_ofNat

/-- info: 'IxCC.BigNat.Entry.val_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_inj

/-- info: 'IxCC.BigNat.Entry.canonical_fromUInt64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_fromUInt64

/-- info: 'IxCC.BigNat.Entry.val_fromUInt64' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_fromUInt64

/-- info: 'IxCC.BigNat.Entry.canonical_fromLimbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_fromLimbs

/-- info: 'IxCC.BigNat.Entry.val_fromLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_fromLimbs

/-- info: 'IxCC.BigNat.Entry.canonical_ofTaggedWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_ofTaggedWord

/-- info: 'IxCC.BigNat.Entry.toTaggedWord?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.toTaggedWord?_spec

/-- info: 'IxCC.BigNat.Entry.ofTaggedWord_toTaggedWord?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.ofTaggedWord_toTaggedWord?

/-- info: 'IxCC.BigNat.Entry.isCanonical_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.isCanonical_iff

/-- info: 'IxCC.BigNat.Entry.cmp_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.cmp_spec

/-- info: 'IxCC.BigNat.Entry.beq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.beq_spec

/-- info: 'IxCC.BigNat.Entry.ble_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.ble_spec

/-- info: 'IxCC.BigNat.Entry.blt_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.blt_spec

/-- info: 'IxCC.BigNat.Entry.canonical_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_add

/-- info: 'IxCC.BigNat.Entry.val_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_add

/-- info: 'IxCC.BigNat.Entry.canonical_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_sub

/-- info: 'IxCC.BigNat.Entry.val_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_sub

/-- info: 'IxCC.BigNat.Entry.canonical_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_pred

/-- info: 'IxCC.BigNat.Entry.val_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_pred

/-- info: 'IxCC.BigNat.Entry.canonical_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_mul

/-- info: 'IxCC.BigNat.Entry.val_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_mul

/-- info: 'IxCC.BigNat.Entry.canonical_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_pow

/-- info: 'IxCC.BigNat.Entry.val_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_pow

/-- info: 'IxCC.BigNat.Entry.pow?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.pow?_spec

/-- info: 'IxCC.BigNat.Entry.canonical_divMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_divMod

/-- info: 'IxCC.BigNat.Entry.divMod_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.divMod_spec

/-- info: 'IxCC.BigNat.Entry.canonical_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_div

/-- info: 'IxCC.BigNat.Entry.val_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_div

/-- info: 'IxCC.BigNat.Entry.canonical_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_mod

/-- info: 'IxCC.BigNat.Entry.val_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_mod

/-- info: 'IxCC.BigNat.Entry.gcdU64_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.gcdU64_toNat

/-- info: 'IxCC.BigNat.Entry.canonical_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_gcd

/-- info: 'IxCC.BigNat.Entry.val_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_gcd

/-- info: 'IxCC.BigNat.Entry.canonical_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_land

/-- info: 'IxCC.BigNat.Entry.val_land' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_land

/-- info: 'IxCC.BigNat.Entry.canonical_lor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_lor

/-- info: 'IxCC.BigNat.Entry.val_lor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_lor

/-- info: 'IxCC.BigNat.Entry.canonical_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_xor

/-- info: 'IxCC.BigNat.Entry.val_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_xor

/-- info: 'IxCC.BigNat.Entry.canonical_shiftLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_shiftLeft

/-- info: 'IxCC.BigNat.Entry.val_shiftLeft_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_shiftLeft_mul

/-- info: 'IxCC.BigNat.Entry.shiftLeft?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.shiftLeft?_spec

/-- info: 'IxCC.BigNat.Entry.canonical_shiftRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_shiftRight

/-- info: 'IxCC.BigNat.Entry.val_shiftRight_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_shiftRight_div

/-- info: 'IxCC.BigNat.Entry.canonical_shiftRightSlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_shiftRightSlow

/-- info: 'IxCC.BigNat.Entry.val_shiftRightSlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_shiftRightSlow

/-- info: 'IxCC.BigNat.Entry.log2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.log2_spec

/-- info: 'IxCC.BigNat.Entry.canonical_log2Slow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_log2Slow

/-- info: 'IxCC.BigNat.Entry.val_log2Slow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.val_log2Slow

/-- info: 'IxCC.BigNat.Entry.canonical_ofDecimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.canonical_ofDecimal

/-- info: 'IxCC.BigNat.Entry.ofDecimal_toDecimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Entry.ofDecimal_toDecimal

/-! ## `IxCC.BigNat.Bootstrap` `LimbOps` Word Equation Fences -/

/-- info: 'IxCC.BigNat.Bootstrap.clz64_eqn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.Bootstrap.clz64_eqn

/-- info: 'IxCC.BigNat.Bootstrap.mulWide64_eqn' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.Bootstrap.mulWide64_eqn

/-- info: 'IxCC.BigNat.Bootstrap.divWide64_eqn' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.Bootstrap.divWide64_eqn

/-- info: 'IxCC.BigNat.Bootstrap.addCarry64_eqn' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.Bootstrap.addCarry64_eqn

/-- info: 'IxCC.BigNat.Bootstrap.subBorrow64_eqn' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.Bootstrap.subBorrow64_eqn

/-! ## `IxCC.Rt.BigNat.Cell` Representation & `.rodata` Literal Fences -/

/-- info: 'IxCC.Rt.BigNat.NatVal.low_bit_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.low_bit_small

/-- info: 'IxCC.Rt.BigNat.NatVal.low_bit_big' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.low_bit_big

/-- info: 'IxCC.Rt.BigNat.NatVal.both_small_iff_and_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.both_small_iff_and_odd

/-- info: 'IxCC.Rt.BigNat.NatVal.and_tz_one_false_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.and_tz_one_false_iff

/-- info: 'IxCC.Rt.BigNat.NatVal.and_tz_one_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.and_tz_one_true_iff

/-- info: 'IxCC.Rt.BigNat.NatVal.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.readback

/-- info: 'IxCC.Rt.BigNat.NatVal.unique_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.unique_val

/-- info: 'IxCC.Rt.BigNat.NatVal.eq_one_iff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.eq_one_iff_zero

/-- info: 'IxCC.Rt.BigNat.NatVal.ofRodataLiteral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.ofRodataLiteral

/-- info: 'IxCC.Rt.BigNat.NatVal.matches_slowNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.matches_slowNat

/-! ## `IxCC.Rt.BigNat.ProofProcs` & `IxCC.Rt.BigNat.Proof` Zero-`natOverflow` Simulation Fences -/

/-- info: 'IxCC.Rt.BigNat.natGcdBig_proc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natGcdBig_proc_spec

/-- info: 'IxCC.Rt.BigNat.natPowBig_proc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natPowBig_proc_spec

/-- info: 'IxCC.Rt.BigNat.natAddBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natAddBig_core

/-- info: 'IxCC.Rt.BigNat.natSubBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natSubBig_core

/-- info: 'IxCC.Rt.BigNat.natPredBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natPredBig_core

/-- info: 'IxCC.Rt.BigNat.natSuccPeelBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natSuccPeelBig_core

/-- info: 'IxCC.Rt.BigNat.natMulBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natMulBig_core

/-- info: 'IxCC.Rt.BigNat.natDivBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natDivBig_core

/-- info: 'IxCC.Rt.BigNat.natModBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natModBig_core

/-- info: 'IxCC.Rt.BigNat.natBeqBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natBeqBig_core

/-- info: 'IxCC.Rt.BigNat.natBleBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natBleBig_core

/-- info: 'IxCC.Rt.BigNat.natBltBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natBltBig_core

/-- info: 'IxCC.Rt.BigNat.natCmpBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natCmpBig_core

/-- info: 'IxCC.Rt.BigNat.natLandBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natLandBig_core

/-- info: 'IxCC.Rt.BigNat.natLorBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natLorBig_core

/-- info: 'IxCC.Rt.BigNat.natXorBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natXorBig_core

/-- info: 'IxCC.Rt.BigNat.natBitBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natBitBig_core

/-- info: 'IxCC.Rt.BigNat.natShrBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natShrBig_core

/-- info: 'IxCC.Rt.BigNat.natShlBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natShlBig_core

/-- info: 'IxCC.Rt.BigNat.natShiftBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natShiftBig_core

/-- info: 'IxCC.Rt.BigNat.natPowBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natPowBig_core

/-- info: 'IxCC.Rt.BigNat.natPowBig_core_of_proc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natPowBig_core_of_proc

/-- info: 'IxCC.Rt.BigNat.natGcdBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natGcdBig_core

/-- info: 'IxCC.Rt.BigNat.natGcdBig_core_of_proc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natGcdBig_core_of_proc

/-- info: 'IxCC.Rt.BigNat.primitiveBig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.primitiveBig_core
