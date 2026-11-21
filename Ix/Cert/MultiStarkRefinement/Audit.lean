import Ix.Cert.MultiStarkRefinement.EndToEnd
import Ix.Cert.MultiStarkRefinement.MutationControl

/-! # Workstream 1A-ii Audit Surface (`Ix.Cert.MultiStarkRefinement.Audit`)

Verifies that every headline theorem in `Ix.Cert.MultiStarkRefinement` (pinning and refining
`MultiStark.recursionProgram` onto `Ix.Cert.MultiStark.verifyBatch` and `EndToEnd`, plus
mutation negative controls) depends ONLY on standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`, zero `bv_decide`).
-/

-- 1. Deployed MultiStark.recursionProgram AST pinning & BLAKE3 digest injectivity
#check @Ix.Cert.MultiStarkRefinement.recursionSource_core_functions_present
#check @Ix.Cert.MultiStarkRefinement.recursionSource_ast_pinned
#check @Ix.Cert.MultiStarkRefinement.recursionProgram_ast_pinned
#check @Ix.Cert.MultiStarkRefinement.packDigest8_inj
/-- info: 'Ix.Cert.MultiStarkRefinement.recursionProgram_ast_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.recursionProgram_ast_pinned
/-- info: 'Ix.Cert.MultiStarkRefinement.packDigest8_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.packDigest8_inj

-- 2. Goldilocks field & extension bridge
#check @Ix.Cert.MultiStarkRefinement.glLtPModel_eq_one_iff
#check @Ix.Cert.MultiStarkRefinement.gl_to_bytes_unique
#check @Ix.Cert.MultiStarkRefinement.gl_inverse_spec
#check @Ix.Cert.MultiStarkRefinement.eg_inverse_spec
#check @Ix.Cert.MultiStarkRefinement.ext_is_zero_iff
#check @Ix.Cert.MultiStarkRefinement.pair_mul_refines
#check @Ix.Cert.MultiStarkRefinement.two_adic_gen_refines
#check @Ix.Cert.MultiStarkRefinement.quotient_degree_of_refines
#check @Ix.Cert.MultiStarkRefinement.rows_pop_canonical_eq
#check @Ix.Cert.MultiStarkRefinement.goldilocks_inv_two_eq
#check @Ix.Cert.MultiStarkRefinement.eg_div_base_eq
#check @Ix.Cert.MultiStarkRefinement.roFoldHorner_refines_tail
#check @Ix.Cert.MultiStarkRefinement.bucket_finalize_distributes
/-- info: 'Ix.Cert.MultiStarkRefinement.gl_to_bytes_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.gl_to_bytes_unique
/-- info: 'Ix.Cert.MultiStarkRefinement.eg_inverse_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.eg_inverse_spec
/-- info: 'Ix.Cert.MultiStarkRefinement.two_adic_gen_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.two_adic_gen_refines
/-- info: 'Ix.Cert.MultiStarkRefinement.rows_pop_canonical_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.rows_pop_canonical_eq
/-- info: 'Ix.Cert.MultiStarkRefinement.eg_div_base_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.eg_div_base_eq
/-- info: 'Ix.Cert.MultiStarkRefinement.roFoldHorner_refines_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.roFoldHorner_refines_tail
/-- info: 'Ix.Cert.MultiStarkRefinement.bucket_finalize_distributes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.bucket_finalize_distributes

-- 3. Wire deserialization, transcript, MMCS, preamble bounds, and verifyBatch refinement
#check @Ix.Cert.MultiStarkRefinement.lookup_groups_count_refines
#check @Ix.Cert.MultiStarkRefinement.wire_decoding_authentic_or_collision
#check @Ix.Cert.MultiStarkRefinement.ch_sample_field_accept_iff
#check @Ix.Cert.MultiStarkRefinement.assert_shard_count_ok_sound
#check @Ix.Cert.MultiStarkRefinement.at_most_row_bound_sound
#check @Ix.Cert.MultiStarkRefinement.bytes8LeModel_eq_one_iff
#check @Ix.Cert.MultiStarkRefinement.closurePairsAccepted_disjoint
#check @Ix.Cert.MultiStarkRefinement.verifyShard_of_witness
#check @Ix.Cert.MultiStarkRefinement.verifyBatch_of_witness
/-- info: 'Ix.Cert.MultiStarkRefinement.closurePairsAccepted_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.closurePairsAccepted_disjoint
/-- info: 'Ix.Cert.MultiStarkRefinement.verifyBatch_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.verifyBatch_of_witness

-- 4. End-to-End Observed Trace Bridge & Recursive Verifier Soundness
#check @Ix.Cert.MultiStarkRefinement.prepared_obs_of_extracted_trace
#check @Ix.Cert.MultiStarkRefinement.recursion_obs_refines_verifyBatch
#check @Ix.Cert.MultiStarkRefinement.recursionProgram_refines_multiStark_verify
#check @Ix.Cert.MultiStarkRefinement.recursive_step_to_ixvm_circuit_sound
/-- info: 'Ix.Cert.MultiStarkRefinement.prepared_obs_of_extracted_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.prepared_obs_of_extracted_trace
/-- info: 'Ix.Cert.MultiStarkRefinement.recursionProgram_refines_multiStark_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.recursionProgram_refines_multiStark_verify
/-- info: 'Ix.Cert.MultiStarkRefinement.recursive_step_to_ixvm_circuit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.recursive_step_to_ixvm_circuit_sound

-- 5. Mutation Negative Controls
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_fails_pin
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_unsound
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_closure_pairs_unsound
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_fails_pin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_fails_pin
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_unsound
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_closure_pairs_unsound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_closure_pairs_unsound
