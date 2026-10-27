/-! Grouping tuned for the certified Aiur layout using measured small and
production workloads. The search accounts for padded rows, main/auxiliary
columns and FFT work; see docs/formal-aiur-grouping-tuning.md.
Physical deduplication is resolved before grouping. Missing/inlined members
are skipped, and entrypoints retain singleton circuits. -/

namespace MultiStark

def functionGroups : List (String × List String) := [
  ("verifier_group_00", ["MultiStark::read_byte_stream", "MultiStark::read_vk_u16", "MultiStark::rev_onto"]),
  ("verifier_group_01", ["Blake3::compress_layer", "Blake3::finish", "MultiStark::read_vk_u64", "MultiStark::active_onto", "MultiStark::digest_eq"]),
  ("verifier_group_02", ["Blake3::next_layer", "MultiStark::assert_closure_pairs", "MultiStark::verify_shard", "MultiStark::ood_loop", "MultiStark::verify_query", "MultiStark::verify_commit_multi", "MultiStark::last_acc"]),
  ("verifier_group_03", ["UInt64::is_zero", "MultiStark::read_merkle_cap_vec_n", "MultiStark::messages_onto_each", "MultiStark::messages_acc", "MultiStark::obs_log_arities", "MultiStark::verify_input_multi", "MultiStark::assert_blowup_zero", "${\"name\":\"MultiStark::list_length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"MultiStark::Bucket\"}}]}"]),
  ("verifier_group_04", ["Blake3::bytes_to_block", "MultiStark::read_digest_vec_at_n", "MultiStark::batch_fiat_shamir", "MultiStark::shard_fiat_shamir", "MultiStark::logup_steps_fold"]),
  ("verifier_group_05", ["Blake3::compress_block", "MultiStark::cap_onto", "MultiStark::b3_rows_chunks", "MultiStark::open_prep"]),
  ("verifier_group_06", ["${\"name\":\"Lists::is_empty\",\"types\":[\"field\"]}", "MultiStark::accs_onto", "MultiStark::select_rows_le", "MultiStark::inject_maybe"]),
  ("verifier_group_07", ["UInt64::wrapping_succ", "MultiStark::read_vk_cap_n", "MultiStark::three_limbs", "MultiStark::bytes8_le", "MultiStark::le_step", "MultiStark::assert_same_cap", "MultiStark::pcs_betas", "MultiStark::pcs_check_witness", "MultiStark::heights_prep", "MultiStark::fri_fold2"]),
  ("verifier_group_08", ["MultiStark::read_vk_u16_limb", "${\"name\":\"MultiStark::list_drop\",\"types\":[\"field\"]}"]),
  ("verifier_group_09", ["MultiStark::read_sys_circuits_n", "MultiStark::read_proof", "MultiStark::log_degree_ok", "MultiStark::mmcs_compress", "MultiStark::verify_one_query"]),
  ("verifier_group_10", ["MultiStark::read_vk_u32_limb", "MultiStark::read_field", "MultiStark::read_sys_lookups_n", "MultiStark::read_batch_opening_vec_n", "MultiStark::claims_onto", "MultiStark::claims_onto_each", "MultiStark::snoc_b8", "MultiStark::reconstruct_ext_row", "MultiStark::prep_count"]),
  ("verifier_group_11", ["UInt32::less_than_fields", "MultiStark::select_rows"]),
  ("verifier_group_12", ["MultiStark::lookup_groups_count", "MultiStark::read_opt_idx_n", "MultiStark::read_claims_n", "MultiStark::log_degrees_onto"]),
  ("verifier_group_13", ["MultiStark::read_opt_commit", "MultiStark::read_header_vec_n", "MultiStark::read_message_vec_n", "MultiStark::select_active_circuits", "MultiStark::quotient_eval", "MultiStark::rollin"]),
  ("verifier_group_14", ["${\"name\":\"MultiStark::list_concat\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":8}}]}", "MultiStark::read_active_n", "MultiStark::read_ext_vec", "${\"name\":\"MultiStark::list_length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"MultiStark::BatchMessage\"}}]}", "MultiStark::heights_all", "MultiStark::frontier_fold"]),
  ("verifier_group_15", ["MultiStark::read_count", "MultiStark::read_proof_vec_n", "MultiStark::assert_shard_count_ok", "${\"name\":\"MultiStark::list_length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"MultiStark::ShardHeader\"}}]}", "${\"name\":\"MultiStark::list_length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"MultiStark::Proof\"}}]}", "MultiStark::claims_acc", "MultiStark::pow2", "${\"name\":\"MultiStark::list_length\",\"types\":[{\"named\":{\"args\":[],\"name\":\"MultiStark::CommitPhaseMultiStep\"}}]}", "MultiStark::build_buckets"]),
  ("verifier_group_16", ["MultiStark::read_u64", "MultiStark::ri_apply"]),
  ("verifier_group_17", ["MultiStark::read_u8", "MultiStark::read_u8_at"]),
  ("verifier_group_18", ["UInt64::to_field", "MultiStark::read_claim_vals_n", "MultiStark::read_digest_vec_at", "MultiStark::headers_onto", "MultiStark::assert_same_bits", "MultiStark::snoc_cap", "MultiStark::bits_to_num", "MultiStark::has_height"]),
  ("verifier_group_19", ["MultiStark::read_count_at", "MultiStark::read_u64_at"]),
  ("verifier_group_20", ["MultiStark::read_u64_vec", "MultiStark::read_u64_vec_n", "${\"name\":\"MultiStark::list_lookup\",\"types\":[\"field\"]}"]),
  ("verifier_group_21", ["MultiStark::read_ext_vec_n", "MultiStark::read_ext_vec_vec_n", "MultiStark::fingerprint_vals"]),
  ("verifier_group_22", ["MultiStark::read_u64_vec_vec_vec_n", "${\"name\":\"MultiStark::list_length\",\"types\":[\"field\"]}", "MultiStark::b3_w4_onto", "MultiStark::batch_views_at"]),
  ("verifier_group_23", ["MultiStark::read_commit_phase_step_vec_n", "MultiStark::select_active_prep", "MultiStark::ext_exp_pow2", "MultiStark::heights_max", "MultiStark::drop_index_bits"]),
  ("verifier_group_24", ["MultiStark::read_ext_vec_vec", "MultiStark::read_opened_round_n", "MultiStark::messages_onto", "MultiStark::assert_bits", "MultiStark::assert_log_degrees_ok", "MultiStark::count_ones"]),
  ("verifier_group_25", ["MultiStark::read_opened_round", "MultiStark::pair_mul", "MultiStark::round_onto", "MultiStark::compress_ordered"]),
  ("verifier_group_26", ["MultiStark::read_preprocessed", "MultiStark::verify_batch", "MultiStark::leaf_hash_at", "MultiStark::frontier_level", "MultiStark::circ_has_height", "MultiStark::rows_at_round"]),
  ("verifier_group_27", ["MultiStark::count_onto", "MultiStark::frontier_merge", "MultiStark::open_prep_batch", "MultiStark::batch_claims"]),
  ("verifier_group_28", ["${\"name\":\"MultiStark::list_length\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":8}}]}", "${\"name\":\"MultiStark::list_lookup\",\"types\":[{\"named\":{\"args\":[],\"name\":\"MultiStark::SysNode\"}}]}"]),
  ("verifier_group_29", ["MultiStark::limbs_onto", "MultiStark::frontier_sort", "MultiStark::frontier_split", "MultiStark::frontier_leaves"]),
  ("verifier_group_30", ["MultiStark::header_onto", "MultiStark::ch_sample8", "MultiStark::verify_shards", "MultiStark::quotient_degree_of", "MultiStark::mmcs_verify_multi"]),
  ("verifier_group_31", ["MultiStark::ch_sample_ext", "MultiStark::ch_sample_field", "MultiStark::query_loop"]),
  ("verifier_group_32", ["${\"name\":\"MultiStark::list_length\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":2}}]}", "MultiStark::sample_query_indices", "MultiStark::query_views", "MultiStark::step_views_at"]),
  ("verifier_group_33", ["UInt64::eq", "${\"name\":\"MultiStark::list_drop\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":2}}]}"]),
  ("verifier_group_34", ["${\"name\":\"MultiStark::list_lookup\",\"types\":[{\"array\":{\"element\":\"field\",\"length\":2}}]}", "MultiStark::fold_roots", "MultiStark::logup_fingerprint", "MultiStark::open_batch_2pt", "MultiStark::open_2pt_mat", "MultiStark::open_quotient"]),
  ("verifier_group_35", ["MultiStark::eval_at", "MultiStark::assert_same_limbs"]),
  ("verifier_group_36", ["${\"name\":\"MultiStark::list_drop\",\"types\":[{\"named\":{\"args\":[],\"name\":\"MultiStark::SysNode\"}}]}", "MultiStark::ood_fold"]),
  ("verifier_group_37", ["MultiStark::from_ext_basis", "MultiStark::points_onto", "MultiStark::assert_same_claims", "MultiStark::exp_by_bits"]),
  ("verifier_group_38", ["MultiStark::bucket_update", "MultiStark::ro_fold"]),
]

end MultiStark
