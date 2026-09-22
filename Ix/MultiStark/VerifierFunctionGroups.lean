module

/-!
Function-grouping data for the standalone Multi-STARK verifier toplevel
(`MultiStark.multiStark`), applied wherever it is compiled for proving or
verifying (see `CompiledToplevel.groupFunctions`). Empty = no grouping:
every constrained function keeps its singleton circuit. Fill from measured
workload statistics; a stale grouping stays sound (grouping never affects
semantics), only less efficient.
-/

public section

namespace MultiStark

-- 20 groups over 139 circuits, cost-aware greedy merging
-- over the ix_aggr join and two standalone-verifier profiles (average 2%,
-- max 4% modelled cost increase per workload).
def verifierFunctionGroups : Array (String × Array String) := #[
  ("verifier_group_00", #[
    "memo_u32_less_than",
    "u64_is_zero",
    "relaxed_u64_succ",
    "flatten_u64",
    "read_sys_lookups_n",
    "frontier_merge",
    "frontier_split",
    "frontier_sort",
    "frontier_leaves",
    "rows_at_round",
    "limbs_onto",
    "from_ext_basis"
  ]),
  ("verifier_group_01", #[
    "address_eq_tail",
    "address_eq"
  ]),
  ("verifier_group_02", #[
    "read_u8",
    "read_digest_vec_at",
    "read_vk_u32_limb",
    "read_field",
    "lookup_groups_count",
    "assert_blowup_zero",
    "ext_exp_pow2",
    "reconstruct_ext_row",
    "assert_bits",
    "select_active_circuits",
    "select_active_prep",
    "list_length.SysCircuit"
  ]),
  ("verifier_group_03", #[
    "read_u64",
    "blake3_next_layer",
    "blake3_compress_layer",
    "read_vk_u64",
    "mmcs_verify_multi",
    "pcs_check_witness",
    "open_prep_batch",
    "query_loop",
    "verify_commit_multi",
    "ch_sample_field",
    "ch_sample_ext",
    "snoc_b8",
    "logup_steps_fold"
  ]),
  ("verifier_group_04", #[
    "read_count",
    "read_opened_round",
    "read_batch_opening_vec_n",
    "read_commit_phase_step_vec_n",
    "read_preprocessed",
    "bytes_to_addr",
    "mmcs_compress",
    "pcs_betas",
    "verify_query",
    "cap_onto",
    "ch_sample_bits",
    "fingerprint_vals",
    "read_claim_vals_n",
    "list_length.Bucket",
    "list_concat.U8_8"
  ]),
  ("verifier_group_05", #[
    "read_count_at",
    "list_drop.SysNode"
  ]),
  ("verifier_group_06", #[
    "read_active_n",
    "read_u64_vec_vec_vec_n",
    "read_opened_round_n",
    "b3_w4_onto",
    "frontier_fold",
    "circ_has_height",
    "heights_all",
    "heights_prep",
    "batch_views_at",
    "step_views_at",
    "drop_index_bits",
    "take_bits"
  ]),
  ("verifier_group_07", #[
    "read_u64_vec",
    "list_length.Ptr.U8_8_4"
  ]),
  ("verifier_group_08", #[
    "read_ext_vec",
    "read_ext_vec_vec",
    "read_ext_vec_vec_n",
    "pad_block",
    "read_vk_u16_limb",
    "has_height",
    "bits_to_num",
    "exp_by_bits",
    "points_onto",
    "round_onto",
    "log_degrees_onto",
    "list_concat.Ptr.U8_32"
  ]),
  ("verifier_group_09", #[
    "read_ext_vec_n",
    "pair_mul"
  ]),
  ("verifier_group_10", #[
    "read_digest_vec_at_n",
    "read_merkle_cap_vec_n",
    "read_opt_idx_n",
    "leaf_hash_at",
    "fri_fold2",
    "obs_log_arities",
    "build_buckets",
    "rollin",
    "sample_query_indices",
    "query_views",
    "snoc_cap",
    "two_adic_gen",
    "pow2",
    "quotient_eval",
    "list_length.CommitPhaseMultiStep"
  ]),
  ("verifier_group_11", #[
    "read_u64_vec_vec_n",
    "read_node_ids_n"
  ]),
  ("verifier_group_12", #[
    "bytes_to_block",
    "blake3_finish",
    "blake3_compress_block",
    "read_sys_circuits_n",
    "ch_sample8",
    "ood_loop"
  ]),
  ("verifier_group_13", #[
    "read_vk_cap_n",
    "read_opt_commit",
    "prep_count",
    "heights_max",
    "verify_one_query",
    "verify_input_multi",
    "quotient_degree_of",
    "claims_acc",
    "read_claims_n",
    "list_length.FrontierNode"
  ]),
  ("verifier_group_14", #[
    "compress_ordered",
    "ood_fold",
    "list_is_empty.Ptr.U8_32"
  ]),
  ("verifier_group_15", #[
    "select_rows_le",
    "frontier_level",
    "accs_onto"
  ]),
  ("verifier_group_16", #[
    "inject_maybe",
    "rev_onto",
    "list_lookup.G_2",
    "list_drop.G_2"
  ]),
  ("verifier_group_17", #[
    "open_2pt_mat",
    "open_batch_2pt",
    "open_quotient",
    "open_prep",
    "fold_roots",
    "logup_fingerprint"
  ]),
  ("verifier_group_18", #[
    "list_lookup.U8_8",
    "list_drop.U8_8"
  ]),
  ("verifier_group_19", #[
    "list_lookup.BatchOpening",
    "list_length.CommitPhaseProofStep",
    "list_drop.G"
  ])
]

end MultiStark

end
