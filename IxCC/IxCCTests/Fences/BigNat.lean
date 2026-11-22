import IxCC.BigNat.Proof

/-! Exact Layer-1 axiom fences for the pure-Lean formally verified `IxCC.BigNat`
library (90 theorems across `LimbOps`, `Basic`, `Linear`, `Mul`, `Div`, and
`GcdConv`). Every theorem depends strictly on subsets of
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

/-! ### Linear (27 fences) -/

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

/-! ### Mul (14 fences) -/

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

/-! ### Div (11 fences) -/

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

/-! ### GcdConv (14 fences) -/

/-- info: 'IxCC.BigNat.wf_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_gcd

/-- info: 'IxCC.BigNat.toNat_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.toNat_gcd

/-- info: 'IxCC.BigNat.wf_mulAdd1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.BigNat.wf_mulAdd1

/-- info: 'IxCC.BigNat.toNat_mulAdd1' depends on axioms: [propext, Quot.sound] -/
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
