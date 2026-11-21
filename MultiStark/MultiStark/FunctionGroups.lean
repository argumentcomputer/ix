/-! Grouping tuned for the certified Aiur layout using measured small and
production workloads. The search accounts for padded rows, main/auxiliary
columns and FFT work; see docs/formal-aiur-grouping-tuning.md.
Physical deduplication is resolved before grouping. Missing/inlined members
are skipped, and entrypoints retain singleton circuits. -/

namespace MultiStark

def functionGroups : List (String × List String) := [
  ("verifier_group_00", ["StarkIO::read_byte_stream", "SystemDeserialize::read_vk_u16", "StarkVerifier::rev_onto"]),
  ("verifier_group_01", ["Blake3::compress_layer", "Blake3::finish", "SystemDeserialize::read_vk_u64", "StarkVerifier::active_onto", "StarkHash::digest_eq"]),
  ("verifier_group_02", ["Blake3::next_layer", "StarkVerifier::assert_closure_pairs", "StarkVerifier::verify_shard", "StarkVerifier::ood_loop", "Pcs::verify_query", "Pcs::verify_commit_multi", "StarkVerifier::last_acc"]),
  ("verifier_group_03", ["UInt64::is_zero", "ProofDeserialize::read_merkle_cap_vec_n", "StarkVerifier::messages_onto_each", "StarkVerifier::messages_acc", "Pcs::obs_log_arities", "Pcs::verify_input_multi", "Pcs::assert_blowup_zero", "${\"name\":\"Lists::length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"Pcs::Bucket\"}}]}"]),
  ("verifier_group_04", ["Blake3::bytes_to_block", "ProofDeserialize::read_digest_vec_at_n", "Transcript::batch_fiat_shamir", "Transcript::shard_fiat_shamir", "StarkVerifier::logup_steps_fold"]),
  ("verifier_group_05", ["Blake3::compress_block", "StarkVerifier::cap_onto", "StarkHash::b3_rows_chunks", "Pcs::open_prep"]),
  ("verifier_group_06", ["${\"name\":\"Lists::is_empty\",\"types\":[\"field\"]}", "StarkVerifier::accs_onto", "Pcs::select_rows_le", "Pcs::inject_maybe"]),
  ("verifier_group_07", ["UInt64::wrapping_succ", "SystemDeserialize::read_vk_cap_n", "StarkVerifier::three_limbs", "StarkVerifier::bytes8_le", "StarkVerifier::le_step", "StarkVerifier::assert_same_cap", "Pcs::pcs_betas", "Pcs::pcs_check_witness", "Pcs::heights_prep", "Pcs::fri_fold2"]),
  ("verifier_group_08", ["SystemDeserialize::read_vk_u16_limb", "${\"name\":\"Lists::drop\",\"types\":[\"field\"]}"]),
  ("verifier_group_09", ["SystemDeserialize::read_sys_circuits_n", "ProofDeserialize::read_proof", "StarkVerifier::log_degree_ok", "Mmcs::mmcs_compress", "Pcs::verify_one_query"]),
  ("verifier_group_10", ["SystemDeserialize::read_vk_u32_limb", "SystemDeserialize::read_field", "SystemDeserialize::read_sys_lookups_n", "ProofDeserialize::read_batch_opening_vec_n", "StarkVerifier::claims_onto", "StarkVerifier::claims_onto_each", "StarkVerifier::snoc_b8", "StarkVerifier::reconstruct_ext_row", "Pcs::prep_count"]),
  ("verifier_group_11", ["UInt32::less_than_fields", "Pcs::select_rows"]),
  ("verifier_group_12", ["SystemDeserialize::lookup_groups_count", "SystemDeserialize::read_opt_idx_n", "StarkVerifier::read_claims_n", "StarkVerifier::log_degrees_onto"]),
  ("verifier_group_13", ["SystemDeserialize::read_opt_commit", "ProofDeserialize::read_header_vec_n", "ProofDeserialize::read_message_vec_n", "StarkVerifier::select_active_circuits", "StarkVerifier::quotient_eval", "Pcs::rollin"]),
  ("verifier_group_14", ["${\"name\":\"Lists::concat\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":8}}]}", "ProofDeserialize::read_active_n", "ProofDeserialize::read_ext_vec", "${\"name\":\"Lists::length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"ProofDeserialize::BatchMessage\"}}]}", "Pcs::heights_all", "Mmcs::frontier_fold"]),
  ("verifier_group_15", ["ProofDeserialize::read_count", "ProofDeserialize::read_proof_vec_n", "StarkVerifier::assert_shard_count_ok", "${\"name\":\"Lists::length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"ProofDeserialize::ShardHeader\"}}]}", "${\"name\":\"Lists::length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"ProofDeserialize::Proof\"}}]}", "StarkVerifier::claims_acc", "StarkVerifier::pow2", "${\"name\":\"Lists::length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"ProofDeserialize::CommitPhaseMultiStep\"}}]}", "Pcs::build_buckets"]),
  ("verifier_group_16", ["ProofDeserialize::read_u64", "Pcs::ri_apply"]),
  ("verifier_group_17", ["ProofDeserialize::read_u8", "ProofDeserialize::read_u8_at"]),
  ("verifier_group_18", ["UInt64::to_field", "StarkVerifier::read_claim_vals_n", "ProofDeserialize::read_digest_vec_at", "StarkVerifier::headers_onto", "StarkVerifier::assert_same_bits", "StarkVerifier::snoc_cap", "Pcs::bits_to_num", "Pcs::has_height"]),
  ("verifier_group_19", ["ProofDeserialize::read_count_at", "ProofDeserialize::read_u64_at"]),
  ("verifier_group_20", ["ProofDeserialize::read_u64_vec", "ProofDeserialize::read_u64_vec_n", "${\"name\":\"Lists::lookup\",\"types\":[\"field\"]}"]),
  ("verifier_group_21", ["ProofDeserialize::read_ext_vec_n", "ProofDeserialize::read_ext_vec_vec_n", "StarkVerifier::fingerprint_vals"]),
  ("verifier_group_22", ["ProofDeserialize::read_u64_vec_vec_vec_n", "${\"name\":\"Lists::length\",\"types\":[\"field\"]}", "StarkHash::b3_w4_onto", "Pcs::batch_views_at"]),
  ("verifier_group_23", ["ProofDeserialize::read_commit_phase_step_vec_n", "StarkVerifier::select_active_prep", "StarkVerifier::ext_exp_pow2", "Pcs::heights_max", "Pcs::drop_index_bits"]),
  ("verifier_group_24", ["ProofDeserialize::read_ext_vec_vec", "ProofDeserialize::read_opened_round_n", "StarkVerifier::messages_onto", "StarkVerifier::assert_bits", "StarkVerifier::assert_log_degrees_ok", "StarkVerifier::count_ones"]),
  ("verifier_group_25", ["ProofDeserialize::read_opened_round", "StarkVerifier::pair_mul", "Pcs::round_onto", "Pcs::compress_ordered"]),
  ("verifier_group_26", ["ProofDeserialize::read_preprocessed", "StarkVerifier::verify_batch", "Pcs::leaf_hash_at", "Mmcs::frontier_level", "Pcs::circ_has_height", "Pcs::rows_at_round"]),
  ("verifier_group_27", ["StarkVerifier::count_onto", "Mmcs::frontier_merge", "Pcs::open_prep_batch", "StarkVerifier::batch_claims"]),
  ("verifier_group_28", ["${\"name\":\"Lists::length\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":8}}]}", "${\"name\":\"Lists::lookup\",\"types\":[{\"named\":{\"args\":[],\"name\":\"SystemDeserialize::SysNode\"}}]}"]),
  ("verifier_group_29", ["StarkVerifier::limbs_onto", "Mmcs::frontier_sort", "Mmcs::frontier_split", "Mmcs::frontier_leaves"]),
  ("verifier_group_30", ["StarkVerifier::header_onto", "Transcript::ch_sample8", "StarkVerifier::verify_shards", "StarkVerifier::quotient_degree_of", "Mmcs::mmcs_verify_multi"]),
  ("verifier_group_31", ["Transcript::ch_sample_ext", "Transcript::ch_sample_field", "Pcs::query_loop"]),
  ("verifier_group_32", ["${\"name\":\"Lists::length\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":2}}]}", "Pcs::sample_query_indices", "Pcs::query_views", "Pcs::step_views_at"]),
  ("verifier_group_33", ["UInt64::eq", "${\"name\":\"Lists::drop\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":2}}]}"]),
  ("verifier_group_34", ["${\"name\":\"Lists::lookup\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":2}}]}", "StarkVerifier::fold_roots", "StarkVerifier::logup_fingerprint", "Pcs::open_batch_2pt", "Pcs::open_2pt_mat", "Pcs::open_quotient"]),
  ("verifier_group_35", ["StarkVerifier::eval_at", "StarkVerifier::assert_same_limbs"]),
  ("verifier_group_36", ["${\"name\":\"Lists::drop\",\"types\":[{\"named\":{\"args\":[],\"name\":\"SystemDeserialize::SysNode\"}}]}", "StarkVerifier::ood_fold"]),
  ("verifier_group_37", ["StarkVerifier::from_ext_basis", "Pcs::points_onto", "StarkVerifier::assert_same_claims", "Pcs::exp_by_bits"]),
  ("verifier_group_38", ["Pcs::bucket_update", "Pcs::ro_fold"]),
]

end MultiStark
