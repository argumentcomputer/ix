import Ix.Cert.MultiStark.EndToEnd

/-! # Workstream 1A-i Audit Surface (`Ix.Cert.MultiStark.Audit`)

Verifies that every headline theorem in the certified Multi-STARK / CertiFRI
stack depends ONLY on the three standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`,
zero `bv_decide`, zero custom axioms).
-/

-- Gap 1a: Goldilocks field model & WellFormed
#check @Ix.Cert.MultiStark.goldilocksFieldModel
#check @Ix.Cert.MultiStark.goldilocksWellFormed
/-- info: 'Ix.Cert.MultiStark.goldilocksWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.goldilocksWellFormed

-- Gap 1b: BLAKE3 pure-specification parity
#check @Ix.Cert.MultiStark.blake3_eq_pure
#check @Ix.Cert.MultiStark.hashPair_eq_pure
#check @Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure
#check @Ix.Cert.MultiStark.extHasher_hashRows_eq_pure
/-- info: 'Ix.Cert.MultiStark.blake3_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.blake3_eq_pure
/-- info: 'Ix.Cert.MultiStark.hashPair_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.hashPair_eq_pure
/-- info: 'Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure
/-- info: 'Ix.Cert.MultiStark.extHasher_hashRows_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.extHasher_hashRows_eq_pure

-- Gap 2: Shape-independent adaptive dynamic ROM
#check @Ix.Cert.MultiStark.fractionLE_projectQueryIndex
#check @Ix.Cert.MultiStark.settles_of_depends_on_digests
#check @Ix.Cert.MultiStark.soundness_dynamic_rom
/-- info: 'Ix.Cert.MultiStark.fractionLE_projectQueryIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.fractionLE_projectQueryIndex
/-- info: 'Ix.Cert.MultiStark.soundness_dynamic_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.soundness_dynamic_rom

-- Gap 3: Unconditional ROM soundness for Plonky3 pruned MMCS
#check @Ix.Cert.MultiStark.soundness_pruned_uniqueDecoding
#check @Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness
#check @Ix.Cert.MultiStark.basePoly_of_eval_c1_zero
/-- info: 'Ix.Cert.MultiStark.soundness_pruned_uniqueDecoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.soundness_pruned_uniqueDecoding
/-- info: 'Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness

-- Gap 4a & 4b: Small-height off-domain decoding & AIR selectors / Horner batching
#check @Ix.Cert.MultiStark.decodeMarginOff_blowup2_all_heights
#check @Ix.Cert.MultiStark.eval_decodeOff_of_claimsHoldOff
#check @Ix.Cert.MultiStark.eval_isFirstPoly_on_domain
#check @Ix.Cert.MultiStark.eval_isLastPoly_on_domain
#check @Ix.Cert.MultiStark.card_horner_bad_le
/-- info: 'Ix.Cert.MultiStark.eval_decodeOff_of_claimsHoldOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.eval_decodeOff_of_claimsHoldOff
/-- info: 'Ix.Cert.MultiStark.card_horner_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.card_horner_bad_le

-- Gap 5: Sharded MEMSEG -> WidthROM.Valid, Plan.checkMemo, and IxVM CircuitSound composition
#check @Ix.Cert.MultiStark.memseg_balance_implies_unique
#check @Ix.Cert.MultiStark.plan_checkMemo_of_field_balance
#check @Ix.Cert.MultiStark.prepared_eval_of_extracted_trace
#check @Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace
/-- info: 'Ix.Cert.MultiStark.memseg_balance_implies_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.memseg_balance_implies_unique
/-- info: 'Ix.Cert.MultiStark.plan_checkMemo_of_field_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.plan_checkMemo_of_field_balance
/-- info: 'Ix.Cert.MultiStark.prepared_eval_of_extracted_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.prepared_eval_of_extracted_trace
/-- info: 'Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace
