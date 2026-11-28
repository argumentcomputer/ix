import IxCC.BigNat.Proof.Entry
import IxCC.BigNat.Bootstrap
import IxCC.Rt.BigNat.Cell
import IxCC.Rt.BigNat.ProofProcs
import IxCC.Rt.BigNat.Proof
import IxCC.Rt.BigNat.LowerBigProof

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

/-! ## `IxCC.Rt.Readback` Arbitrary-Precision `readbackBig` Fences -/

/-- info: 'IxCC.Rt.readbackNatWord_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readbackNatWord_small

/-- info: 'IxCC.Rt.readbackBig_nat_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readbackBig_nat_small

/-- info: 'IxCC.Rt.readbackBig_ctor0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readbackBig_ctor0

/-- info: 'IxCC.Rt.readbackBig_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readbackBig_cell

/-- info: 'IxCC.Rt.readbackBig_nat_eq_readback_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readbackBig_nat_eq_readback_of_odd

/-- info: 'IxCC.Rt.readWordsList_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readWordsList_congr

/-- info: 'IxCC.Rt.readbackNatWord_congr_read64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readbackNatWord_congr_read64

/-- info: 'IxCC.Rt.readbackBig_congr_read64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.readbackBig_congr_read64

/-! ## `IxCC.Rt.BigNat.Cell` Kernel-Evaluable `.rodata` `*K` & Readback Equivalence Fences -/

/-- info: 'IxCC.Rt.BigNat.encodeStaticLimbArrayK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.encodeStaticLimbArrayK_eq

/-- info: 'IxCC.Rt.BigNat.encodeBigNatLiteralK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.encodeBigNatLiteralK_eq

/-- info: 'IxCC.Rt.BigNat.addBigNatLiteralK_toRodataTable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.addBigNatLiteralK_toRodataTable

/-- info: 'IxCC.Rt.BigNat.readWordsList_eq_readWordsRange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.readWordsList_eq_readWordsRange

/-- info: 'IxCC.Rt.BigNat.limbsToNatList_eq_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.limbsToNatList_eq_toNat

/-- info: 'IxCC.Rt.BigNat.isCanonicalLimbsList_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.isCanonicalLimbsList_iff

/-- info: 'IxCC.Rt.BigNat.isCanonicalLimbsList_eq_isCanonicalBigNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.isCanonicalLimbsList_eq_isCanonicalBigNat

/-- info: 'IxCC.Rt.BigNat.readbackNatWord_eq_readbackBigNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.readbackNatWord_eq_readbackBigNat

/-- info: 'IxCC.Rt.BigNat.NatVal.readbackBig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.NatVal.readbackBig

/-! ## `IxCC.Rt.BigNat.LowerBigProof` Structural Zero-`natOverflow`, `.rodata` & Simulation Fences -/

/-- info: 'IxCC.Rt.BigNat.lirProgramNoOvf_iff_checkEmpty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.lirProgramNoOvf_iff_checkEmpty

/-- info: 'IxCC.Rt.BigNat.lirStep_ne_natOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.lirStep_ne_natOverflow

/-- info: 'IxCC.Rt.BigNat.semStep_ne_natOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.semStep_ne_natOverflow

/-- info: 'IxCC.Rt.BigNat.failsNoOvf_of_noNatOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.failsNoOvf_of_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.lirRun_ne_natOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.lirRun_ne_natOverflow

/-- info: 'IxCC.Rt.BigNat.lirEval_ne_natOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.lirEval_ne_natOverflow

/-- info: 'IxCC.Rt.BigNat.functionBig_noNatOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.functionBig_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.arrayPrimFuncBig_noNatOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.arrayPrimFuncBig_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.functionRepBig_noNatOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.functionRepBig_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.bigNatLitProc_noNatOverflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.bigNatLitProc_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.cxInit_noNatOverflow' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.cxInit_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.natPowBig_noNatOverflow' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natPowBig_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.natGcdBig_noNatOverflow' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natGcdBig_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.extendedArrayRuntimeFuncs_noNatOverflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.extendedArrayRuntimeFuncs_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.buildCoreWrappers_noNatOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.buildCoreWrappers_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.lowerBig_noNatOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.lowerBig_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.lowerRepBig_noNatOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.lowerRepBig_noNatOverflow

/-- info: 'IxCC.Rt.BigNat.buildBigNatRodataK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.buildBigNatRodataK_eq

/-- info: 'IxCC.Rt.BigNat.buildBigNatRodata_entry_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.buildBigNatRodata_entry_bytes

/-- info: 'IxCC.Rt.BigNat.buildBigNatRodata_natVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.buildBigNatRodata_natVal

/-- info: 'IxCC.Rt.BigNat.readbackBig_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.readbackBig_congr

/-- info: 'IxCC.Rt.BigNat.natSwitchBig_isZero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.natSwitchBig_isZero_iff

/-- info: 'IxCC.Rt.BigNat.operandBig_nat_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.operandBig_nat_sim

/-- info: 'IxCC.Rt.BigNat.primitiveBig_sim_readback_noOvf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.primitiveBig_sim_readback_noOvf

/-- info: 'IxCC.Rt.BigNat.projBig_natSucc_sim_readback_noOvf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.BigNat.projBig_natSucc_sim_readback_noOvf
