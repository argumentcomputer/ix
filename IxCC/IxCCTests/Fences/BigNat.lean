import IxCC.BigNat.Proof
import IxCC.Nat.Rep

/-! Exact Layer-1 axiom fences for the pure-Lean formally verified `IxCC.BigNat`
library (166 theorems across `LimbOps`, `Basic`, `Linear`, `Toom3`, `Mul`, `InvDiv`,
`Div`, `Lehmer`, and `GcdConv`) and for the two representation primitives of
arbitrary-precision `Nat` (`IxCC.Nat.Rep`, 53 theorems: the specification over limb lists,
`limbsBijection`, `toLimbs`, `ofLimbs` and their canonical equations).
Every theorem depends strictly on subsets of
`[propext, Classical.choice, Quot.sound]` — zero `sorryAx`, zero
`Lean.ofReduceBool` / `Lean.trustCompiler`, zero custom axioms.
Expected messages are preserved verbatim. -/

/-! ### LimbOps (10 fences) -/

/-- info: 'IxCC.BigNat.addCarry64_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.addCarry64_spec

/-- info: 'IxCC.BigNat.subBorrow64_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.subBorrow64_spec

/-- info: 'IxCC.BigNat.mulWide64_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.mulWide64_spec

/-- info: 'IxCC.BigNat.divWide64_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divWide64_fst

/-- info: 'IxCC.BigNat.divWide64_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divWide64_snd

/-- info: 'IxCC.BigNat.divWide64_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divWide64_spec

/-- info: 'IxCC.BigNat.clz64_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.BigNat.clz64_zero

/-- info: 'IxCC.BigNat.clz64_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.clz64_spec

/-- info: 'IxCC.BigNat.clz64_shift_norm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.clz64_shift_norm

/-- info: 'IxCC.BigNat.mulAddCarry64_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.mulAddCarry64_spec

/-! ### Basic (14 fences) -/

/-- info: 'IxCC.BigNat.wf_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.BigNat.wf_zero

/-- info: 'IxCC.BigNat.wf_one' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.BigNat.wf_one

/-- info: 'IxCC.BigNat.toNat_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_inj

/-- info: 'IxCC.BigNat.wf_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_normalize

/-- info: 'IxCC.BigNat.toNat_normalize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_normalize

/-- info: 'IxCC.BigNat.normalize_of_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.normalize_of_wf

/-- info: 'IxCC.BigNat.wf_ofUInt64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_ofUInt64

/-- info: 'IxCC.BigNat.toNat_ofUInt64' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_ofUInt64

/-- info: 'IxCC.BigNat.wf_ofSmall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_ofSmall

/-- info: 'IxCC.BigNat.toNat_ofSmall' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_ofSmall

/-- info: 'IxCC.BigNat.wf_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_ofNat

/-- info: 'IxCC.BigNat.toNat_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_ofNat

/-- info: 'IxCC.BigNat.toSmall?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toSmall?_spec

/-- info: 'IxCC.BigNat.testBit_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.testBit_toNat

/-! ### Linear (66 fences) -/

/-- info: 'IxCC.BigNat.cmp_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.cmp_spec

/-- info: 'IxCC.BigNat.beq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.beq_spec

/-- info: 'IxCC.BigNat.ble_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.ble_spec

/-- info: 'IxCC.BigNat.blt_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.blt_spec

/-- info: 'IxCC.BigNat.wf_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_add

/-- info: 'IxCC.BigNat.toNat_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_add

/-- info: 'IxCC.BigNat.wf_subRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_subRaw

/-- info: 'IxCC.BigNat.toNat_subRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_subRaw

/-- info: 'IxCC.BigNat.wf_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_sub

/-- info: 'IxCC.BigNat.toNat_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_sub

/-- info: 'IxCC.BigNat.wf_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_pred

/-- info: 'IxCC.BigNat.toNat_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_pred

/-- info: 'IxCC.BigNat.wf_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_land

/-- info: 'IxCC.BigNat.toNat_land' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_land

/-- info: 'IxCC.BigNat.wf_lor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_lor

/-- info: 'IxCC.BigNat.toNat_lor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_lor

/-- info: 'IxCC.BigNat.wf_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_xor

/-- info: 'IxCC.BigNat.toNat_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_xor

/-- info: 'IxCC.BigNat.wf_shiftLimbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_shiftLimbs

/-- info: 'IxCC.BigNat.toNat_shiftLimbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftLimbs

/-- info: 'IxCC.BigNat.wf_shiftLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_shiftLeft

/-- info: 'IxCC.BigNat.toNat_shiftLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftLeft

/-- info: 'IxCC.BigNat.toNat_shiftLeft_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftLeft_mul

/-- info: 'IxCC.BigNat.wf_shiftRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_shiftRight

/-- info: 'IxCC.BigNat.toNat_shiftRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftRight

/-- info: 'IxCC.BigNat.toNat_shiftRight_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftRight_div

/-- info: 'IxCC.BigNat.log2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.log2_spec

/-- info: 'IxCC.BigNat.size_copyAppendLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.size_copyAppendLoop

/-- info: 'IxCC.BigNat.size_copyIntoZeros' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.size_copyIntoZeros

/-- info: 'IxCC.BigNat.getLimb_copyIntoZeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.getLimb_copyIntoZeros

/-- info: 'IxCC.BigNat.toNat_copyIntoZeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_copyIntoZeros

/-- info: 'IxCC.BigNat.size_shiftLeft1Loop_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.size_shiftLeft1Loop_le

/-- info: 'IxCC.BigNat.toNat_shiftLeft1Loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftLeft1Loop

/-- info: 'IxCC.BigNat.size_shiftLeft1_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.size_shiftLeft1_le

/-- info: 'IxCC.BigNat.wf_shiftLeft1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_shiftLeft1

/-- info: 'IxCC.BigNat.toNat_shiftLeft1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftLeft1

/-- info: 'IxCC.BigNat.size_shiftRight1Loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.size_shiftRight1Loop

/-- info: 'IxCC.BigNat.getLimb_shiftRight1Loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.getLimb_shiftRight1Loop

/-- info: 'IxCC.BigNat.size_shiftRight1_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.size_shiftRight1_le

/-- info: 'IxCC.BigNat.wf_shiftRight1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_shiftRight1

/-- info: 'IxCC.BigNat.toNat_shiftRight1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftRight1

/-- info: 'IxCC.BigNat.wf_shiftLeftSmall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_shiftLeftSmall

/-- info: 'IxCC.BigNat.toNat_shiftLeftSmall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftLeftSmall

/-- info: 'IxCC.BigNat.wf_shiftRightSmall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_shiftRightSmall

/-- info: 'IxCC.BigNat.toNat_shiftRightSmall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_shiftRightSmall

/-- info: 'IxCC.BigNat.size_addCarryAtLoop_ge' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.size_addCarryAtLoop_ge

/-- info: 'IxCC.BigNat.toNat_addCarryAtLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_addCarryAtLoop

/-- info: 'IxCC.BigNat.toNat_addAtLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_addAtLoop

/-- info: 'IxCC.BigNat.toNat_addAtInPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_addAtInPlace

/-- info: 'IxCC.BigNat.toNat_addInPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_addInPlace

/-- info: 'IxCC.BigNat.size_subBorrowAtLoop' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.size_subBorrowAtLoop

/-- info: 'IxCC.BigNat.toNat_subBorrowAtLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_subBorrowAtLoop

/-- info: 'IxCC.BigNat.size_subAtLoop' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.size_subAtLoop

/-- info: 'IxCC.BigNat.toNat_subAtLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_subAtLoop

/-- info: 'IxCC.BigNat.subAtInPlace_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.subAtInPlace_spec

/-- info: 'IxCC.BigNat.toNat_subAtInPlace_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_subAtInPlace_of_le

/-- info: 'IxCC.BigNat.wf_subInPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_subInPlace

/-- info: 'IxCC.BigNat.toNat_subInPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_subInPlace

/-- info: 'IxCC.BigNat.subMulCarry64_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.subMulCarry64_spec

/-- info: 'IxCC.BigNat.toNat_addMul1AtLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_addMul1AtLoop

/-- info: 'IxCC.BigNat.toNat_addMul1AtInPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_addMul1AtInPlace

/-- info: 'IxCC.BigNat.toNat_addMul1InPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_addMul1InPlace

/-- info: 'IxCC.BigNat.size_subMul1AtLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.size_subMul1AtLoop

/-- info: 'IxCC.BigNat.toNat_subMul1AtLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_subMul1AtLoop

/-- info: 'IxCC.BigNat.subMul1AtInPlace_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.subMul1AtInPlace_spec

/-- info: 'IxCC.BigNat.subMul1InPlace_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.subMul1InPlace_spec

/-! ### Toom3 (13 fences) -/

/-- info: 'IxCC.BigNat.inv3_64_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.inv3_64_toNat

/-- info: 'IxCC.BigNat.inv3_64_mul_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.inv3_64_mul_three

/-- info: 'IxCC.BigNat.wf_divExact3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_divExact3

/-- info: 'IxCC.BigNat.divExact3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divExact3_spec

/-- info: 'IxCC.BigNat.wf_signedSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_signedSub

/-- info: 'IxCC.BigNat.signedSub_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.signedSub_spec

/-- info: 'IxCC.BigNat.wf_karatsubaCombine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_karatsubaCombine

/-- info: 'IxCC.BigNat.toNat_karatsubaCombine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_karatsubaCombine

/-- info: 'IxCC.BigNat.toom3EvalLoop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toom3EvalLoop_eq

/-- info: 'IxCC.BigNat.wf_toom3Interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_toom3Interp

/-- info: 'IxCC.BigNat.toom3Interp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toom3Interp_spec

/-- info: 'IxCC.BigNat.wf_toom3Combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_toom3Combine

/-- info: 'IxCC.BigNat.toNat_toom3Combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_toom3Combine

/-! ### Mul (18 fences) -/

/-- info: 'IxCC.BigNat.wf_mulSchoolbook' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_mulSchoolbook

/-- info: 'IxCC.BigNat.toNat_mulSchoolbook' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_mulSchoolbook

/-- info: 'IxCC.BigNat.wf_sqrSchoolbook' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_sqrSchoolbook

/-- info: 'IxCC.BigNat.toNat_sqrSchoolbook' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_sqrSchoolbook

/-- info: 'IxCC.BigNat.wf_mulKaratsuba' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_mulKaratsuba

/-- info: 'IxCC.BigNat.toNat_mulKaratsuba' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_mulKaratsuba

/-- info: 'IxCC.BigNat.wf_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_mul

/-- info: 'IxCC.BigNat.toNat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_mul

/-- info: 'IxCC.BigNat.wf_sqrKaratsuba' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_sqrKaratsuba

/-- info: 'IxCC.BigNat.toNat_sqrKaratsuba' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_sqrKaratsuba

/-- info: 'IxCC.BigNat.wf_sqr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_sqr

/-- info: 'IxCC.BigNat.toNat_sqr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_sqr

/-- info: 'IxCC.BigNat.wf_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_pow

/-- info: 'IxCC.BigNat.toNat_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_pow

/-- info: 'IxCC.BigNat.wf_mulToom3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_mulToom3

/-- info: 'IxCC.BigNat.toNat_mulToom3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_mulToom3

/-- info: 'IxCC.BigNat.wf_sqrToom3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_sqrToom3

/-- info: 'IxCC.BigNat.toNat_sqrToom3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_sqrToom3

/-! ### InvDiv (8 fences) -/

/-- info: 'IxCC.BigNat.shift_or_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.shift_or_toNat

/-- info: 'IxCC.BigNat.invert21_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.invert21_spec

/-- info: 'IxCC.BigNat.invert21_eq_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.invert21_eq_div

/-- info: 'IxCC.BigNat.divRem21_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divRem21_spec

/-- info: 'IxCC.BigNat.divRem21_eq_divWide64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divRem21_eq_divWide64

/-- info: 'IxCC.BigNat.shiftLeft_clz64_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.shiftLeft_clz64_ge

/-- info: 'IxCC.BigNat.wf_divMod1Inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_divMod1Inv

/-- info: 'IxCC.BigNat.divMod1Inv_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divMod1Inv_spec

/-! ### Div (16 fences) -/

/-- info: 'IxCC.BigNat.wf_divMod1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_divMod1

/-- info: 'IxCC.BigNat.divMod1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divMod1_spec

/-- info: 'IxCC.BigNat.toNat_divMod1_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_divMod1_lt

/-- info: 'IxCC.BigNat.trialQhat_theorem_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.trialQhat_theorem_B

/-- info: 'IxCC.BigNat.wf_divMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_divMod

/-- info: 'IxCC.BigNat.divMod_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divMod_spec

/-- info: 'IxCC.BigNat.wf_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_div

/-- info: 'IxCC.BigNat.toNat_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_div

/-- info: 'IxCC.BigNat.wf_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_mod

/-- info: 'IxCC.BigNat.toNat_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_mod

/-- info: 'IxCC.BigNat.toNat_mod_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_mod_lt

/-- info: 'IxCC.BigNat.ge_two_pow_63_of_shr63_ne_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.BigNat.ge_two_pow_63_of_shr63_ne_zero

/-- info: 'IxCC.BigNat.trialQhatInv_eq_trialQhat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.trialQhatInv_eq_trialQhat

/-- info: 'IxCC.BigNat.divModKnuth_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divModKnuth_spec

/-- info: 'IxCC.BigNat.divQuick1_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.divQuick1_spec

/-- info: 'IxCC.BigNat.div_eq_divMod_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.div_eq_divMod_fst

/-! ### Lehmer (7 fences) -/

/-- info: 'IxCC.BigNat.gcdWord64_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.gcdWord64_spec

/-- info: 'IxCC.BigNat.wf_linCombSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_linCombSub

/-- info: 'IxCC.BigNat.linCombSub_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.linCombSub_spec

/-- info: 'IxCC.BigNat.lehmerStep_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.lehmerStep_gcd

/-- info: 'IxCC.BigNat.lehmerStep_decrease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.lehmerStep_decrease

/-- info: 'IxCC.BigNat.wf_gcdLehmer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_gcdLehmer

/-- info: 'IxCC.BigNat.toNat_gcdLehmer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_gcdLehmer

/-! ### GcdConv (14 fences) -/

/-- info: 'IxCC.BigNat.wf_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_gcd

/-- info: 'IxCC.BigNat.toNat_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_gcd

/-- info: 'IxCC.BigNat.wf_mulAdd1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_mulAdd1

/-- info: 'IxCC.BigNat.toNat_mulAdd1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_mulAdd1

/-- info: 'IxCC.BigNat.toDecimalChunks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toDecimalChunks_spec

/-- info: 'IxCC.BigNat.wf_ofDecimalChunks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_ofDecimalChunks

/-- info: 'IxCC.BigNat.toNat_ofDecimalChunks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_ofDecimalChunks

/-- info: 'IxCC.BigNat.ofDecimalChunks_toDecimalChunks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.ofDecimalChunks_toDecimalChunks

/-- info: 'IxCC.BigNat.toDecimalDigits_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toDecimalDigits_spec

/-- info: 'IxCC.BigNat.wf_ofDecimalDigits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_ofDecimalDigits

/-- info: 'IxCC.BigNat.toNat_ofDecimalDigits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_ofDecimalDigits

/-- info: 'IxCC.BigNat.ofDecimalDigits_toDecimalDigits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.ofDecimalDigits_toDecimalDigits

/-- info: 'IxCC.BigNat.wf_ofDecimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_ofDecimal

/-- info: 'IxCC.BigNat.ofDecimal_toDecimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.ofDecimal_toDecimal

/-! ### Representation primitives `toLimbs` / `ofLimbs` (`IxCC.Nat.Rep`, 53 fences) -/

/-- info: 'IxCC.NatRep.limbBase_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.limbBase_eq

/-- info: 'IxCC.NatRep.limbBase_pos' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.limbBase_pos

/-- info: 'IxCC.NatRep.one_lt_limbBase' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.one_lt_limbBase

/-- info: 'IxCC.NatRep.natOfLimbs_nil' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.natOfLimbs_nil

/-- info: 'IxCC.NatRep.natOfLimbs_cons' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.natOfLimbs_cons

/-- info: 'IxCC.NatRep.limbsFuel_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_zero

/-- info: 'IxCC.NatRep.limbsFuel_succ' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_succ

/-- info: 'IxCC.NatRep.limbsFuel_zero_right' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_zero_right

/-- info: 'IxCC.NatRep.limbsFuel_succ_of_ne' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_succ_of_ne

/-- info: 'IxCC.NatRep.div_limbBase_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.div_limbBase_le

/-- info: 'IxCC.NatRep.natOfLimbs_limbsFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.natOfLimbs_limbsFuel

/-- info: 'IxCC.NatRep.limbsFuel_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_lt

/-- info: 'IxCC.NatRep.limbsFuel_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_ne_nil

/-- info: 'IxCC.NatRep.limbsFuel_getLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_getLast

/-- info: 'IxCC.NatRep.canonical_limbsFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.canonical_limbsFuel

/-- info: 'IxCC.NatRep.natOfLimbs_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.natOfLimbs_pos

/-- info: 'IxCC.NatRep.canonical_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.NatRep.canonical_tail

/-- info: 'IxCC.NatRep.limbsFuel_natOfLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_natOfLimbs

/-- info: 'IxCC.NatRep.limbsBijection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsBijection

/-- info: 'IxCC.NatRep.natOfLimbs_limbsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.natOfLimbs_limbsOf

/-- info: 'IxCC.NatRep.canonical_limbsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.canonical_limbsOf

/-- info: 'IxCC.NatRep.limbsOf_natOfLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsOf_natOfLimbs

/-- info: 'IxCC.NatRep.limbsFuel_eq_limbsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsFuel_eq_limbsOf

/-- info: 'IxCC.NatRep.limbsOf_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.limbsOf_zero

/-- info: 'IxCC.NatRep.limbsOf_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbsOf_of_ne

/-- info: 'IxCC.NatRep.natOfLimbs_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.natOfLimbs_inj

/-- info: 'IxCC.NatRep.natOfLimbs_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.natOfLimbs_lt

/-- info: 'IxCC.NatRep.le_natOfLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.le_natOfLimbs

/-- info: 'IxCC.NatRep.toLimbsFuel_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.toLimbsFuel_zero

/-- info: 'IxCC.NatRep.toLimbsFuel_succ' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.toLimbsFuel_succ

/-- info: 'IxCC.NatRep.ofNat_mod_limbBase' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.NatRep.ofNat_mod_limbBase

/-- info: 'IxCC.NatRep.toNat_ofNat_of_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.NatRep.toNat_ofNat_of_lt

/-- info: 'IxCC.NatRep.toList_toLimbsFuel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.NatRep.toList_toLimbsFuel

/-- info: 'IxCC.NatRep.toList_toLimbs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.NatRep.toList_toLimbs

/-- info: 'IxCC.NatRep.map_toNat_map_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.map_toNat_map_ofNat

/-- info: 'IxCC.NatRep.map_ofNat_map_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.map_ofNat_map_toNat

/-- info: 'IxCC.NatRep.toLimbs_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.toLimbs_spec

/-- info: 'IxCC.NatRep.ofLimbs_mk_nil' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.ofLimbs_mk_nil

/-- info: 'IxCC.NatRep.ofLimbs_mk_cons' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.ofLimbs_mk_cons

/-- info: 'IxCC.NatRep.foldr_eq_natOfLimbs' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.foldr_eq_natOfLimbs

/-- info: 'IxCC.NatRep.ofLimbs_spec' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.ofLimbs_spec

/-- info: 'IxCC.NatRep.limbs_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.limbs_lt

/-- info: 'IxCC.NatRep.canonical_toLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.canonical_toLimbs

/-- info: 'IxCC.NatRep.ofLimbs_toLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.ofLimbs_toLimbs

/-- info: 'IxCC.NatRep.toLimbs_ofLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.toLimbs_ofLimbs

/-- info: 'IxCC.NatRep.toLimbs_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.toLimbs_inj

/-- info: 'IxCC.NatRep.toLimbs_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.toLimbs_zero

/-- info: 'IxCC.NatRep.toList_toLimbs_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.toList_toLimbs_of_ne

/-- info: 'IxCC.NatRep.lt_pow_size_toLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.lt_pow_size_toLimbs

/-- info: 'IxCC.NatRep.pow_size_toLimbs_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.pow_size_toLimbs_le

/-- info: 'IxCC.NatRep.toLimbs_eqn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.NatRep.toLimbs_eqn

/-- info: 'IxCC.NatRep.ofLimbs_nil_eqn' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.NatRep.ofLimbs_nil_eqn

/-- info: 'IxCC.NatRep.ofLimbs_cons_eqn' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.NatRep.ofLimbs_cons_eqn
