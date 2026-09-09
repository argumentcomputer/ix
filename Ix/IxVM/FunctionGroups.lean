module

/-!
Function-grouping data for the IxVM kernel toplevel, applied wherever the
kernel is compiled for proving or verifying (see
`CompiledToplevel.groupFunctions`). Empty = no grouping: every constrained
function keeps its singleton circuit. Fill from measured workload
statistics; a stale grouping stays sound (grouping never affects
semantics), only less efficient.
-/

public section

namespace IxVM

-- Cost-aware greedy grouping over the String.split / Array.extract_append
-- kernel-check profiles and a 2^16384 big-nat reduction: merges are ranked
-- by active committed width saved (proof size) per unit of modelled prover
-- cost (FFT model plus a constraint-evaluation term, relative to each
-- workload), capped at 16 members and 40 selectors per group, within an
-- average 2% (max 4%) cost increase per workload. 83 groups over 656 of
-- 743 groupable circuits: 744 -> 171 circuits.
def functionGroups : Array (String × Array String) := #[
  ("ixvm_group_00", #[
    "memo_u32_less_than",
    "lbr_max",
    "lbr_min",
    "delta_unfold"
  ]),
  ("ixvm_group_01", #[
    "address_eq_tail",
    "get_recursor",
    "count_ctors",
    "ctor_at",
    "load_verified_blob",
    "get_ci",
    "check_canonical_block",
    "peer_agree_walk",
    "ind_is_solo",
    "flat_originals_walk",
    "find_peer_recursor_with_spec"
  ]),
  ("ixvm_group_02", #[
    "u64_eq",
    "relaxed_u64_succ",
    "quot_kind_tag",
    "klimbs_mod",
    "system_platform_get_num_bits_addr",
    "str_addr",
    "convert_axiom",
    "convert_quotient",
    "quot_ctor_addr",
    "quot_lift_addr_iota",
    "quot_ind_addr",
    "quot_type_addr"
  ]),
  ("ixvm_group_03", #[
    "u64_add",
    "is_str_prim_addr",
    "is_dec_prim_addr",
    "check_const"
  ]),
  ("ixvm_group_04", #[
    "relaxed_u64_pred",
    "flatten_u64"
  ]),
  ("ixvm_group_05", #[
    "verify_bytes_against",
    "put_constructor_proj",
    "get_expr_let",
    "build_succ_chain",
    "bytes_to_u64_limb",
    "io_peel_field_loop",
    "assert_occ_param_bvars",
    "populate_rules",
    "build_minor_doms",
    "peel_leading_foralls_acc",
    "flat_find_matching",
    "const_idxs_rules"
  ]),
  ("ixvm_group_06", #[
    "bytes_to_addr",
    "get_constructor",
    "get_mut_const",
    "is_unit_like_type",
    "canon_muts_has_kind",
    "is_muts_block",
    "muts_indc_count_is_one",
    "const_idxs_ctors"
  ]),
  ("ixvm_group_07", #[
    "blake3_next_layer",
    "get_ci_iprj",
    "get_ci_cprj",
    "muts_member_at",
    "projection_addr",
    "build_flat_block",
    "run_claim"
  ]),
  ("ixvm_group_08", #[
    "blake3_compress_layer",
    "blake3_finish",
    "get_constant"
  ]),
  ("ixvm_group_09", #[
    "put_expr",
    "get_ci_rprj",
    "first_recr_parent_block",
    "load_assumption_tree",
    "env_walk",
    "get_mut_entry",
    "get_mut_entry_list_inner",
    "check_opt_addr",
    "check_muts_components",
    "list_length_u64.MutConst",
    "list_lookup_u64.Constructor"
  ]),
  ("ixvm_group_10", #[
    "put_u64_le",
    "check_native_nat",
    "utf8_last_go",
    "char_lit_codepoint",
    "mk_nat_binop_stuck",
    "canon_cmp_krec_rule_ctx",
    "canon_kind_ord",
    "canon_ctor_ctx_entries",
    "canon_refine_one",
    "canon_ins_sort",
    "canon_flatten",
    "canon_all_singleton",
    "extract_aux_spec_params_from_rec",
    "check_opt_u64",
    "list_concat.Tup.Ptr.U8_32.G",
    "rbtree_map_insert.G"
  ]),
  ("ixvm_group_11", #[
    "put_tag0",
    "put_tag4",
    "put_definition_proj",
    "convert_definition",
    "level_reduce",
    "compare_struct_fields",
    "try_unfold_head",
    "k_infer_lit",
    "list_any_mentions_block",
    "check_inductive_shape",
    "list_reverse.G"
  ]),
  ("ixvm_group_12", #[
    "put_tag2",
    "univ_succ_base",
    "put_recursor_rule",
    "put_mut_const",
    "u64_or",
    "u64_xor_kbits",
    "defn_member_recur_addrs",
    "canon_cmp_member_ctx",
    "canon_sort_loop",
    "aux_already_in",
    "spec_params_dom_prefix_match",
    "addr_set_build",
    "env_walk_refs",
    "env_walk_leaves",
    "expr_addr",
    "rbtree_map_balance.G"
  ]),
  ("ixvm_group_13", #[
    "put_u64_list",
    "put_recursor_rule_list",
    "canon_g_list_eq",
    "canon_ctx_class_idx",
    "canon_cmp_kexpr_ctx",
    "canon_member_ci",
    "canon_member_num_ctors",
    "canon_refine_classes",
    "canon_group_consec",
    "level_list_struct_eq",
    "spec_params_ptr_eq",
    "flat_find_pos",
    "get_opt_rule_list_masked",
    "get_opt_ctor_entry_list_masked",
    "list_length.U8_8"
  ]),
  ("ixvm_group_14", #[
    "put_quot_kind",
    "pack_def_kind_safety",
    "mk_nat_literal_64",
    "mk_nat_one",
    "char_of_nat_addr",
    "char_type_addr",
    "byte_array_empty_addr",
    "utf8_last_codepoint",
    "utf8_cont",
    "canon_ord_then",
    "canon_sord_then",
    "def_safety_tag",
    "check_opt_bool",
    "check_opt_recr_rules",
    "check_opt_ctor_entries",
    "run_contains"
  ]),
  ("ixvm_group_15", #[
    "put_all_mode",
    "klimbs_shl",
    "np_whnf_inner_bv",
    "canon_addr_chunk",
    "canon_cmp_kliteral",
    "leaf_hash",
    "node_hash",
    "addr_set_member",
    "get_opt_u64_masked",
    "get_opt_addr_masked",
    "get_opt_bool_masked",
    "get_opt_def_kind_masked",
    "get_opt_quot_kind_masked",
    "check_opt_def_kind",
    "check_opt_def_safety",
    "check_opt_quot_kind"
  ]),
  ("ixvm_group_16", #[
    "app_telescope_count",
    "lam_telescope_count",
    "all_telescope_count",
    "put_app_telescope",
    "put_lam_telescope",
    "put_all_telescope",
    "put_definition",
    "put_constructor",
    "put_inductive",
    "str_lit_delta_step",
    "canon_cmp_ctor_range_ctx",
    "canon_group_walk",
    "get_reveal_rule_list_inner",
    "check_recr_rules",
    "rbtree_map_lookup_or_default.G",
    "rbtree_map_ins.G"
  ]),
  ("ixvm_group_17", #[
    "put_address",
    "u64_mul",
    "try_reduce_decide_bitvec_lt",
    "try_nat_binop_addr",
    "build_rec_type_from",
    "check_recursor_canonical_full"
  ]),
  ("ixvm_group_18", #[
    "univ_succ_count",
    "put_univ",
    "put_axiom",
    "put_quotient",
    "put_constructor_list",
    "put_mut_const_list",
    "klimbs_lor",
    "klimbs_xor_op",
    "canon_cmp_klimbs_tail",
    "extract_aux_occ_us",
    "detect_aux_from_recrs_ex",
    "get_ctor_entry",
    "check_ctor_entries",
    "list_length_u64.U8_8",
    "list_length_u64.Constructor",
    "list_length_u64.RecursorRule"
  ]),
  ("ixvm_group_19", #[
    "put_expr_list",
    "get_recursor_rule_list",
    "get_inductive",
    "canon_indc_positions",
    "check_block_peer_param_agreement",
    "flat_find_pos_kind",
    "build_rec_type",
    "build_flat_own_params",
    "build_all_minors_walk",
    "build_all_motives_walk",
    "const_idxs_muts",
    "list_length_u64.Ptr.U8_32"
  ]),
  ("ixvm_group_20", #[
    "put_univ_list",
    "put_address_list",
    "put_sharing",
    "klimbs_dec",
    "mk_nat_offset_stuck",
    "idx_to_u64",
    "nlvars_eq",
    "se_scan_fields",
    "se_addr_in",
    "compute_iprj_addr",
    "flat_member_at",
    "collect_index_doms",
    "collect_n_doms_whnf",
    "wrap_lams",
    "is_rec_field_peel"
  ]),
  ("ixvm_group_21", #[
    "put_recursor",
    "klimbs_scalar_value",
    "str_dec_eq_build",
    "canon_addr_cmp",
    "canon_cmp_member_same_kind_ctx",
    "canon_cmp_ctor_pair_ctx",
    "get_reveal_ctor_info",
    "get_ctor_entry_list_inner",
    "check_opt_expr_addr",
    "check_ctor_entry",
    "check_mut_const",
    "run_reveal"
  ]),
  ("ixvm_group_22", #[
    "put_constant_info",
    "put_constant",
    "convert_inductive",
    "convert_constructor",
    "convert_recursor",
    "const_idxs_of",
    "check_muts_member_at"
  ]),
  ("ixvm_group_23", #[
    "put_refs",
    "put_univs",
    "klimbs_le",
    "check_no_dep_data_field_if_prop",
    "assert_return_head_is_parent",
    "caddr_is_peer",
    "rec_to_parent_addr",
    "peel_motive_params_subst",
    "list_lift_indices",
    "build_peer_recs",
    "list_lift_each",
    "check_rec_major_spine",
    "get_opt_addr",
    "list_length.Tup.Ptr.U8_32.G.Ptr.ListNode.Ptr.KExprNode.Ptr.ListNode.Ptr.KLevelNode"
  ]),
  ("ixvm_group_24", #[
    "read_byte",
    "klimbs_mul",
    "expr_inst1_bvar",
    "unfold_b_and_loop",
    "peel_n_foralls"
  ]),
  ("ixvm_group_25", #[
    "get_tag2",
    "get_constructor_proj",
    "level_max",
    "whnf_iota_major",
    "collect_spine_of_ctor"
  ]),
  ("ixvm_group_26", #[
    "get_lam_telescope",
    "get_all_telescope"
  ]),
  ("ixvm_group_27", #[
    "get_univ",
    "klimbs_sub_borrow",
    "try_same_proj_head_app"
  ]),
  ("ixvm_group_28", #[
    "get_univ_list",
    "level_max_offsets",
    "projection_definition_info",
    "whnf_struct_core_proj",
    "slow2_eager_fallback",
    "lazy_delta_a_const_b_proj",
    "lazy_delta_b_const_a_proj"
  ]),
  ("ixvm_group_29", #[
    "get_address_list",
    "list_snoc.U8_8"
  ]),
  ("ixvm_group_30", #[
    "unpack_def_kind_safety",
    "assert_wire_bool",
    "defn_is_unsafe_ci",
    "lbr_dec",
    "delta_rank",
    "is_defn_or_thm",
    "is_unsafe_ci",
    "check_parent_inductive_shape",
    "build_all_motives",
    "build_all_minors",
    "build_ctor_app_params"
  ]),
  ("ixvm_group_31", #[
    "get_definition",
    "cleanup_nat_offset_major",
    "convert_univ_idxs",
    "k_is_def_eq_slow2"
  ]),
  ("ixvm_group_32", #[
    "get_axiom",
    "get_quotient",
    "bv_to_nat_via",
    "bitvec_of_nat_args_direct",
    "mk_int_prim",
    "klimbs_eq",
    "bitvec_prep_spine",
    "quot_extract_arg",
    "struct_block_member_addrs",
    "try_eta_expand",
    "check_eq_type"
  ]),
  ("ixvm_group_33", #[
    "get_constructor_list",
    "get_mut_const_list",
    "load_verified_constant",
    "build_recur_addrs_walk",
    "check_muts_all"
  ]),
  ("ixvm_group_34", #[
    "get_inductive_proj",
    "klimbs_is_zero",
    "k_is_def_eq_struct_safe",
    "try_eta_swap",
    "run_check"
  ]),
  ("ixvm_group_35", #[
    "get_constant_info_by_variant",
    "run_check_transitive"
  ]),
  ("ixvm_group_36", #[
    "klimbs_succ",
    "is_nat_succ_ih_step",
    "bytes_to_limbs",
    "convert_rec_rules",
    "nl_eq",
    "nlvars_dominates",
    "dec_dispatch_le_eq",
    "ctors_before_pos",
    "projection_addr_ctor"
  ]),
  ("ixvm_group_37", #[
    "u64_sub_with_borrow",
    "try_nat_offset_dispatch",
    "nl_covers_const",
    "normalize_int_dec_rebuild",
    "check_valid_ind_app",
    "is_large_eliminator",
    "compute_k_target",
    "build_motive_type_flat",
    "canonical_rules_at_pos",
    "build_rule_rhs",
    "check_recursor_member"
  ]),
  ("ixvm_group_38", #[
    "glimbs_to_klimbs",
    "try_match_nat_add",
    "level_normalize",
    "level_max_go",
    "ctx_close_cut",
    "nat_lit_to_ctor_or_self"
  ]),
  ("ixvm_group_39", #[
    "klimbs_sub",
    "skip_bytes",
    "level_explicit_val",
    "expr_has_bvar_at_let",
    "build_param_lvls_range",
    "build_major_params",
    "build_apply_xs",
    "apply_indices_in_conclusion",
    "count_foralls_body",
    "peel_leading_foralls",
    "build_rec_lvls_list",
    "check_rec_rules_wellscoped",
    "list_lookup_or_default.Ptr.U8_32"
  ]),
  ("ixvm_group_40", #[
    "klimbs_div_mod",
    "klimbs_pow",
    "try_nat_linear_rec",
    "check_ctor_return_type",
    "check_inductive_shape_ctors",
    "peel_ctor_params_subst",
    "walk_fields_classify"
  ]),
  ("ixvm_group_41", #[
    "klimbs_div",
    "klimbs_gcd",
    "klimbs_shr",
    "mk_bool",
    "try_quot_iota",
    "se_parent_addr",
    "struct_is_rec",
    "struct_scan_ctors",
    "intern_int_lit",
    "all_bvars_in_args",
    "args_contain_bvar"
  ]),
  ("ixvm_group_42", #[
    "u64_and",
    "klimbs_land",
    "try_reduce_subtype_val",
    "try_str_to_byte_array",
    "try_int_prim_second",
    "try_quot_lift",
    "k_synth_gate",
    "dec_finish",
    "canon_cprj_addr"
  ]),
  ("ixvm_group_43", #[
    "nat_zero_addr",
    "nat_succ_addr_iota",
    "nat_pred_addr",
    "nat_sub_addr",
    "nat_xor_addr",
    "nat_shift_right_addr",
    "punit_size_of_1_addr",
    "reduce_bool_addr",
    "reduce_nat_addr",
    "string_utf8_byte_size_addr",
    "string_append_addr",
    "string_of_list_addr",
    "string_back_addr",
    "string_legacy_back_addr",
    "string_to_byte_array_addr",
    "string_dec_eq_addr"
  ]),
  ("ixvm_group_44", #[
    "int_of_nat_addr",
    "int_neg_succ_addr_dec",
    "bool_true_addr",
    "bool_false_addr",
    "bit_vec_of_nat_addr",
    "bit_vec_addr",
    "lt_lt_addr",
    "decidable_rec_addr",
    "decidable_is_true_addr_dec",
    "decidable_is_false_addr_dec",
    "nat_le_of_ble_eq_true_addr_dec",
    "nat_eq_of_beq_eq_true_addr_dec",
    "nat_ne_of_beq_eq_false_addr_dec",
    "bool_type_addr_dec",
    "eq_refl_addr_dec",
    "eq_type_addr"
  ]),
  ("ixvm_group_45", #[
    "int_add_addr",
    "int_mul_addr",
    "int_neg_addr",
    "int_emod_addr",
    "int_ediv_addr",
    "int_bmod_addr",
    "int_bdiv_addr",
    "int_nat_abs_addr",
    "int_pow_addr",
    "bit_vec_to_nat_addr",
    "bit_vec_ult_addr",
    "decidable_decide_addr",
    "fin_addr",
    "int_dec_eq_addr_dec",
    "int_dec_le_addr_dec",
    "int_dec_lt_addr_dec"
  ]),
  ("ixvm_group_46", #[
    "int_sub_addr",
    "nat_add_addr",
    "nat_mul_addr",
    "nat_pow_addr",
    "nat_gcd_addr",
    "nat_mod_addr",
    "nat_div_addr",
    "nat_land_addr",
    "nat_lor_addr",
    "nat_shift_left_addr",
    "nat_beq_addr",
    "nat_ble_addr",
    "nat_addr_io",
    "nat_dec_le_addr_dec",
    "nat_dec_eq_addr_dec",
    "nat_dec_lt_addr_dec"
  ]),
  ("ixvm_group_47", #[
    "system_platform_num_bits_addr",
    "subtype_val_addr",
    "mk_nat_lit",
    "build_recur_addrs",
    "level_eq",
    "nl_add_const",
    "check_prop_field_if_prop",
    "validate_univ_params_list",
    "check_param_agreement",
    "expr_mentions_block",
    "build_motive_apps",
    "is_rec_field"
  ]),
  ("ixvm_group_48", #[
    "is_native_prim_addr",
    "nl_add_var",
    "expr_lbr_let",
    "expr_lift_bvar",
    "validate_univ_params_seen"
  ]),
  ("ixvm_group_49", #[
    "try_native_dispatch",
    "try_str_dispatch",
    "str_lit_to_ctor",
    "nlvars_add",
    "nlvars_subsume"
  ]),
  ("ixvm_group_50", #[
    "check_native_bool",
    "bitvec_prep_spine_ult",
    "build_char_list",
    "char_lit_codepoint_syn",
    "int_ediv_prim",
    "int_bmod_prim",
    "nlvars_max_offset",
    "nlvars_any_offset_geq",
    "canon_ord_cmp_g",
    "canon_cmp_krec_rule_list_ctx",
    "run_check_env"
  ]),
  ("ixvm_group_51", #[
    "is_bitvec_prim_addr",
    "try_extract_nat_app",
    "nl_skip_empty",
    "whnf_get_ctor_or_none",
    "is_prop_type",
    "get_result_sort_level"
  ]),
  ("ixvm_group_52", #[
    "try_reduce_bit_vec_ult",
    "try_str_back",
    "walk_char_list_bytes",
    "int_bdiv_prim",
    "try_quot_ind",
    "try_str_dec_eq",
    "canon_cmp_u64_lex",
    "canon_build_ctx_members",
    "canon_insert_sorted"
  ]),
  ("ixvm_group_53", #[
    "try_bitvec_dispatch",
    "try_nat_binop_dispatch",
    "glist_cmp",
    "nl_add_const_go",
    "try_normalize_int_decidable",
    "try_dec_dispatch"
  ]),
  ("ixvm_group_54", #[
    "list_nil_addr",
    "list_cons_addr",
    "nat_not_le_of_not_ble_eq_true_addr_dec",
    "canon_sord_lt_strong",
    "canon_sord_eq_strong",
    "canon_sord_gt_strong",
    "canon_sord_of_g"
  ]),
  ("ixvm_group_55", #[
    "utf8_validate",
    "try_extract_nat",
    "glist_eq_len",
    "normalize_aux",
    "assert_lvls_are_params",
    "check_field_universes",
    "addr_list_contains",
    "wrap_foralls",
    "list_reverse_acc.G"
  ]),
  ("ixvm_group_56", #[
    "utf8_decode_one",
    "is_int_prim_addr",
    "try_int_prim_dispatch",
    "glist_ordered_insert",
    "try_iota",
    "check_positivity_aug"
  ]),
  ("ixvm_group_57", #[
    "str_lit_to_ctor_app_or_self",
    "level_offset_of",
    "ctx_next_cut"
  ]),
  ("ixvm_group_58", #[
    "klimbs_from_g",
    "canon_cmp_kuniv_list",
    "canon_cmp_bytes",
    "kexpr_struct_eq",
    "parse_atree_body"
  ]),
  ("ixvm_group_59", #[
    "utf8_encode_prepend",
    "get_ci_dprj",
    "aux_from_recrs_walk_ex",
    "find_peer_rec_spec_walk",
    "get_reveal_mut_const_info",
    "get_reveal_info",
    "list_lookup_u64.MutConst"
  ]),
  ("ixvm_group_60", #[
    "try_extract_int_prim",
    "literal_eq",
    "is_int_dec_prim_addr",
    "try_extract_int",
    "check_quot",
    "check_nested_ctors_positivity",
    "check_large_walk_fields",
    "subst_param_for",
    "ctor_subst_param_for"
  ]),
  ("ixvm_group_61", #[
    "int_add_prim",
    "normalize_imax_dispatch",
    "has_bvar_in_range_let",
    "expr_lift_let",
    "apply_n_projs",
    "se_peel_tol",
    "se_mentions",
    "count_foralls_at_least",
    "check_large_prop_ctor"
  ]),
  ("ixvm_group_62", #[
    "int_emod_prim",
    "canon_ctx_cmp_addr",
    "canon_cmp_kuniv",
    "canon_cmp_klimbs",
    "canon_build_ctx_classes",
    "canon_classes_eq",
    "extract_aux_spec_params",
    "spec_params_lower",
    "apply_spec_params_lifted",
    "list_snoc.Tup.Ptr.U8_32.G.Ptr.ListNode.Ptr.KExprNode.Ptr.ListNode.Ptr.KLevelNode"
  ]),
  ("ixvm_group_63", #[
    "build_succ_offset",
    "try_k_synth_iota",
    "lazy_delta_step_const_const",
    "try_lazy_delta_app",
    "dec_rewrite_lt_to_le",
    "dec_build_proof",
    "compare_rules",
    "apply_ihs_full",
    "build_minor_at_depth",
    "build_ih_doms"
  ]),
  ("ixvm_group_64", #[
    "convert_univ",
    "nl_le_vars",
    "level_imax",
    "expr_glb_let",
    "replace_spine_major",
    "k_is_def_eq_slow_nd_after_core",
    "check_param_agreement_go",
    "check_field_universes_inner"
  ]),
  ("ixvm_group_65", #[
    "level_is_not_zero",
    "nl_subsumption_walk",
    "level_inst_params",
    "whnf_spine",
    "try_proof_irrel"
  ]),
  ("ixvm_group_66", #[
    "glist_subset",
    "nl_subsume_entry",
    "try_nat_dispatch_prewhnf",
    "try_struct_eta_iota",
    "k_infer_proj"
  ]),
  ("ixvm_group_67", #[
    "nl_covers_var",
    "nl_le",
    "level_leq",
    "find_rule",
    "ensure_sort_only",
    "level_list_eq",
    "unfold_both_and_loop",
    "is_inductive_prop",
    "peel_field_loop",
    "peel_n_lams_collect",
    "list_length.KRecRule"
  ]),
  ("ixvm_group_68", #[
    "level_equal",
    "expr_inst1_let",
    "expr_inst_many_let",
    "k_is_def_eq_struct_go",
    "check_positivity_fields",
    "check_positivity",
    "build_apply_field_bvars"
  ]),
  ("ixvm_group_69", #[
    "level_struct_eq",
    "peel_params_subst",
    "k_is_def_eq_structure_tree_app",
    "peel_n_alls_whnf"
  ]),
  ("ixvm_group_70", #[
    "level_max_subsumes",
    "k_is_def_eq_slow",
    "k_is_def_eq_structure_tree"
  ]),
  ("ixvm_group_71", #[
    "level_list_inst",
    "k_is_def_eq_slow_nd",
    "try_unit_like"
  ]),
  ("ixvm_group_72", #[
    "has_bvar_in_range_binder",
    "k_is_def_eq_struct",
    "assert_safety"
  ]),
  ("ixvm_group_73", #[
    "ctx_seek_cut",
    "try_unfold_proj_app"
  ]),
  ("ixvm_group_74", #[
    "ctx_trim",
    "try_reduce_projection_definition"
  ]),
  ("ixvm_group_75", #[
    "expr_has_bvar_at_binder",
    "k_is_def_eq_ordered"
  ]),
  ("ixvm_group_76", #[
    "whnf_proj_head",
    "whnf_nd_proj_head"
  ]),
  ("ixvm_group_77", #[
    "try_reduce_fin_val_decidable_rec",
    "prim_family"
  ]),
  ("ixvm_group_78", #[
    "whnf_struct_core_const",
    "k_is_def_eq_struct_spend"
  ]),
  ("ixvm_group_79", #[
    "const_num_lvls",
    "const_type_of"
  ]),
  ("ixvm_group_80", #[
    "k_infer_only",
    "try_eta_struct"
  ]),
  ("ixvm_group_81", #[
    "k_is_def_eq_core",
    "try_def_eq_nat"
  ]),
  ("ixvm_group_82", #[
    "slow2_after_delta",
    "unfold_a_and_loop",
    "lazy_delta_both_proj",
    "assert_first_args_are_param_bvars",
    "check_field_universes_skip_params",
    "peel_n_foralls_with_types"
  ])
]

end IxVM

end
