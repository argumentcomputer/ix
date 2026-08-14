module

/-!
Circuit-grouping data for the IxVM kernel toplevel, applied wherever the
kernel is compiled for proving or verifying (see
`CompiledToplevel.groupFunctions`). Empty = no grouping: every constrained
function keeps its singleton circuit. Fill from measured workload
statistics; a stale grouping stays sound (grouping never affects
semantics), only less efficient.
-/

public section

namespace IxVM

-- Shape-proximity bands over cold circuits (max FFT share < 0.5% on the
-- String.split / Array.extract_append kernel-check workloads; aux within
-- 1.6x, lookups within max(2x, +4), summed selectors <= 40; verify_claim
-- excluded as the entry). 85 bands over 630 of 709 function circuits:
-- 730 -> 185 circuits. See cold-groups/kernel-shape-grouping2.md.
def coldGroups : Array (String × Array String) := #[
  ("k_shape_00", #[
    "canon_kind_ord",
    "canon_sord_eq_strong",
    "canon_sord_gt_strong",
    "canon_sord_lt_strong",
    "canon_sord_of_g",
    "check_opt_bool",
    "check_opt_u64",
    "const_num_lvls",
    "const_type_of",
    "def_safety_tag",
    "flatten_u64"
  ]),
  ("k_shape_01", #[
    "pack_def_kind_safety",
    "quot_kind_tag",
    "unpack_def_kind_safety",
    "check_opt_ctor_entries",
    "check_opt_recr_rules"
  ]),
  ("k_shape_02", #[
    "canon_ord_then",
    "canon_sord_then",
    "defn_is_unsafe_ci",
    "delta_rank",
    "is_unsafe_ci",
    "lbr_dec",
    "relaxed_u64_pred",
    "relaxed_u64_succ"
  ]),
  ("k_shape_03", #[
    "u64_eq",
    "u64_is_zero",
    "addr_set_member",
    "assert_wire_bool",
    "bit_vec_addr",
    "bit_vec_of_nat_addr",
    "bit_vec_to_nat_addr",
    "bit_vec_ult_addr",
    "bool_false_addr",
    "bool_true_addr",
    "bool_type_addr_dec",
    "build_all_minors",
    "build_all_motives",
    "build_recur_addrs",
    "byte_array_empty_addr",
    "canon_addr_chunk",
    "canon_cmp_kliteral",
    "char_of_nat_addr",
    "char_type_addr",
    "check_parent_inductive_shape"
  ]),
  ("k_shape_04", #[
    "decidable_decide_addr",
    "decidable_is_false_addr_dec",
    "decidable_is_true_addr_dec",
    "decidable_rec_addr",
    "eq_refl_addr_dec",
    "fin_addr",
    "int_dec_eq_addr_dec",
    "int_dec_le_addr_dec",
    "int_dec_lt_addr_dec",
    "int_neg_succ_addr_dec",
    "int_of_nat_addr_dec",
    "k_is_def_eq_struct",
    "klimbs_add",
    "list_cons_addr",
    "list_nil_addr",
    "literal_eq",
    "lt_lt_addr",
    "mk_nat_lit",
    "nat_add_addr",
    "nat_addr_io",
    "nat_beq_addr",
    "nat_ble_addr",
    "nat_dec_eq_addr_dec",
    "nat_dec_le_addr_dec",
    "nat_dec_lt_addr_dec",
    "nat_div_addr",
    "nat_eq_of_beq_eq_true_addr_dec",
    "nat_gcd_addr",
    "nat_land_addr",
    "nat_le_of_ble_eq_true_addr_dec",
    "nat_lor_addr",
    "nat_mod_addr",
    "nat_mul_addr",
    "nat_ne_of_beq_eq_false_addr_dec",
    "nat_not_le_of_not_ble_eq_true_addr_dec",
    "nat_pow_addr",
    "nat_pred_addr"
  ]),
  ("k_shape_05", #[
    "nat_shift_left_addr",
    "nat_shift_right_addr",
    "nat_sub_addr",
    "nat_succ_addr_iota",
    "nat_xor_addr",
    "nat_zero_addr",
    "punit_addr",
    "punit_size_of_1_addr",
    "put_constant_info",
    "put_quot_kind",
    "quot_ctor_addr",
    "quot_ind_addr",
    "quot_lift_addr_iota",
    "quot_type_addr",
    "reduce_bool_addr",
    "reduce_nat_addr",
    "size_of_size_of_addr",
    "str_addr",
    "string_append_addr",
    "string_back_addr",
    "string_dec_eq_addr",
    "string_legacy_back_addr",
    "string_of_list_addr",
    "string_to_byte_array_addr",
    "string_utf8_byte_size_addr",
    "subtype_val_addr",
    "system_platform_get_num_bits_addr",
    "system_platform_num_bits_addr",
    "unit_addr",
    "utf8_last_codepoint"
  ]),
  ("k_shape_06", #[
    "check_param_agreement",
    "is_defn_or_thm",
    "assert_safety",
    "build_ctor_app_params",
    "extract_aux_spec_params_from_rec",
    "is_rec_field",
    "klimbs_div",
    "klimbs_mod",
    "check_opt_def_kind",
    "check_opt_def_safety",
    "check_opt_quot_kind",
    "convert_axiom",
    "convert_quotient",
    "has_bvar_in_range_binder",
    "k_check",
    "klimbs_mul",
    "list_reverse.G",
    "put_definition_proj",
    "put_mut_const",
    "run_contains",
    "utf8_cont",
    "check_inductive_shape"
  ]),
  ("k_shape_07", #[
    "get_opt_addr_masked",
    "get_opt_bool_masked",
    "get_opt_def_kind_masked",
    "get_opt_quot_kind_masked",
    "list_is_empty.U8",
    "defn_member_recur_addrs",
    "expr_inst1_bvar",
    "k_is_def_eq_ordered",
    "klimbs_shl_limbs",
    "klimbs_sub",
    "pad_block",
    "put_u64_le",
    "try_unfold_head",
    "env_walk_leaves",
    "expr_glb_binder"
  ]),
  ("k_shape_08", #[
    "has_bvar_in_range_let",
    "k_infer",
    "k_infer_lit",
    "klimbs_dec",
    "klimbs_gcd",
    "mk_nat_literal_64",
    "mk_nat_one",
    "put_constructor_proj",
    "validate_univ_params_list",
    "get_opt_addr",
    "list_lookup_or_default.Ptr.U8_32",
    "nl_add_const",
    "read_byte",
    "apply_indices_in_conclusion",
    "apply_n_projs",
    "build_apply_field_bvars",
    "build_apply_xs",
    "build_major_params",
    "build_motive_apps",
    "build_param_lvls_range",
    "build_rec_lvls_list"
  ]),
  ("k_shape_09", #[
    "canon_ctor_ctx_entries",
    "check_prop_field_if_prop",
    "mk_bool",
    "np_whnf_inner_bv",
    "peel_leading_foralls",
    "unfold_a_and_loop",
    "unfold_b_and_loop",
    "check_positivity",
    "expr_inst1_let",
    "expr_inst_many_let",
    "expr_lift_let",
    "klimbs_shl",
    "klimbs_shr",
    "leaf_hash",
    "level_equal",
    "count_foralls_body",
    "expr_inst_levels",
    "level_offset_of",
    "skip_bytes",
    "canon_all_singleton",
    "canon_flatten",
    "canon_ins_sort",
    "canon_refine_one"
  ]),
  ("k_shape_10", #[
    "check_field_universes",
    "check_rec_rules_wellscoped",
    "convert_definition",
    "ctx_next_cut",
    "level_max_subsumes",
    "list_reverse_acc.G",
    "put_address_list",
    "utf8_validate",
    "wrap_foralls",
    "wrap_lams",
    "check_positivity_fields",
    "check_quot",
    "env_walk_refs",
    "put_tag0",
    "put_tag2"
  ]),
  ("k_shape_11", #[
    "put_tag4",
    "try_proof_irrel",
    "walk_refs_transitive",
    "convert_constructor",
    "convert_inductive",
    "expr_glb_let",
    "node_hash",
    "rbtree_map_insert.G",
    "check_native_nat",
    "count_foralls_at_least",
    "level_explicit_val",
    "list_length.KRecRule",
    "peel_n_foralls",
    "rbtree_map_balance.G",
    "se_peel_tol",
    "addr_list_contains",
    "all_bvars_in_args"
  ]),
  ("k_shape_12", #[
    "char_lit_codepoint",
    "check_field_universes_skip_params",
    "is_large_eliminator",
    "is_nat_zero",
    "k_ensure_sort",
    "k_is_def_eq_slow",
    "level_is_not_zero",
    "list_any_mentions_block",
    "list_concat.Tup.Ptr.U8_32.G",
    "list_take.Ptr.KExprNode",
    "se_addr_in",
    "str_lit_to_ctor_app_or_self"
  ]),
  ("k_shape_13", #[
    "utf8_last_go",
    "apply_spec_params_lifted",
    "canon_cmp_member_ctx",
    "canon_group_consec",
    "canon_refine_classes",
    "check_no_dep_data_field_if_prop",
    "compare_struct_fields",
    "const_idxs_exprs",
    "level_inst_params",
    "level_list_inst",
    "level_reduce",
    "list_lift_each",
    "list_lift_indices",
    "nl_subsumption_walk",
    "whnf_spine"
  ]),
  ("k_shape_14", #[
    "const_idxs_of",
    "k_is_def_eq",
    "try_unit_like",
    "canon_cmp_klimbs",
    "expr_lbr_let",
    "mk_nat_binop_stuck",
    "replace_spine_major"
  ]),
  ("k_shape_15", #[
    "list_length.Tup.Ptr.U8_32.G.Ptr.ListNode.Ptr.KExprNode.Ptr.ListNode.Ptr.KLevelNode",
    "assert_lvls_are_params",
    "canon_ctx_class_idx",
    "canon_g_list_eq",
    "check_large_prop_ctor",
    "glist_eq_len",
    "peel_leading_foralls_acc",
    "se_scan_fields",
    "canon_build_ctx_classes",
    "canon_cmp_krec_rule_ctx",
    "get_expr_let",
    "nl_le_vars",
    "normalize_aux"
  ]),
  ("k_shape_16", #[
    "try_string_lit_one",
    "canon_ctx_cmp_addr",
    "canon_sort_loop",
    "check_field_universes_inner",
    "intern_int_lit",
    "spec_params_lower",
    "try_quot_iota",
    "unfold_both_and_loop",
    "convert_recursor",
    "assert_first_args_are_param_bvars",
    "assert_occ_param_bvars",
    "head_addr",
    "list_snoc.Tup.Ptr.U8_32.G.Ptr.ListNode.Ptr.KExprNode.Ptr.ListNode.Ptr.KLevelNode",
    "peel_n_foralls_with_types",
    "check_rec_major_spine",
    "get_result_sort_level"
  ]),
  ("k_shape_17", #[
    "io_peel_field_loop",
    "level_list_struct_eq",
    "peel_motive_params_subst",
    "peel_n_alls_whnf",
    "spec_params_ptr_eq",
    "try_extract_nat",
    "whnf_get_ctor_or_none",
    "expr_inst_levels_walk",
    "is_inductive_prop",
    "k_is_def_eq_slow_nd"
  ]),
  ("k_shape_18", #[
    "level_leq",
    "peel_field_loop",
    "level_normalize",
    "u64_and",
    "u64_or",
    "u64_xor_kbits"
  ]),
  ("k_shape_19", #[
    "find_rule",
    "args_contain_bvar",
    "peel_n_lams_collect",
    "build_peer_recs",
    "canon_classes_eq",
    "de_args",
    "expr_mentions_block"
  ]),
  ("k_shape_20", #[
    "lazy_delta_loop",
    "level_eq",
    "level_list_eq",
    "canon_cmp_bytes"
  ]),
  ("k_shape_21", #[
    "canon_cmp_kuniv",
    "canon_cmp_kuniv_list",
    "extract_aux_spec_params",
    "idx_to_u64",
    "normalize_imax_dispatch",
    "spec_params_dom_prefix_match",
    "check_native_bool"
  ]),
  ("k_shape_22", #[
    "is_bitvec_prim_addr",
    "is_int_dec_prim_addr",
    "lazy_delta_both_proj",
    "whnf_nd_apply_beta",
    "canonical_rules_at_pos",
    "mk_nat_offset_stuck"
  ]),
  ("k_shape_23", #[
    "get_opt_u64_masked",
    "flat_find_pos",
    "put_refs",
    "put_sharing",
    "put_univs",
    "try_eta_swap",
    "aux_already_in",
    "is_prop_type",
    "level_struct_eq",
    "nl_skip_empty",
    "peel_params_subst"
  ]),
  ("k_shape_24", #[
    "se_mentions",
    "whnf_nd_with_spine",
    "nl_covers_var",
    "parse_atree_body",
    "try_extract_nat_app",
    "try_unfold_proj_app",
    "klimbs_from_g",
    "get_inductive_proj",
    "list_length.U8_8",
    "canon_cmp_kexpr_ctx",
    "ensure_sort_only"
  ]),
  ("k_shape_25", #[
    "flat_member_at",
    "rec_to_parent_addr",
    "check_param_agreement_go",
    "k_is_def_eq_struct_safe",
    "nl_le",
    "nlvars_eq"
  ]),
  ("k_shape_26", #[
    "build_char_list",
    "build_motive_type_flat",
    "k_def_eq_rebase",
    "klimbs_pow"
  ]),
  ("k_shape_27", #[
    "get_opt_ctor_entry_list_masked",
    "get_opt_rule_list_masked",
    "klimbs_is_zero",
    "klimbs_le",
    "list_snoc.U8_8",
    "put_u64_list",
    "convert_univ",
    "se_parent_addr"
  ]),
  ("k_shape_28", #[
    "kexpr_struct_eq",
    "level_imax",
    "lbr_max",
    "lbr_min"
  ]),
  ("k_shape_29", #[
    "level_max_go",
    "memo_u32_less_than",
    "bitvec_of_nat_args_direct",
    "glimbs_to_klimbs",
    "quot_extract_arg",
    "bv_to_nat_via",
    "nl_add_var",
    "check_ctor_return_type"
  ]),
  ("k_shape_30", #[
    "canon_member_num_ctors",
    "put_recursor_rule_list",
    "run_check",
    "get_axiom",
    "extract_aux_occ_us",
    "whnf",
    "whnf_nd"
  ]),
  ("k_shape_31", #[
    "canon_ord_cmp_g",
    "put_constant",
    "walk_fields_classify",
    "check_large_walk_fields",
    "expr_lift_bvar",
    "dec_dispatch_le_eq",
    "nat_lit_to_ctor_or_self",
    "try_eta_expand",
    "klimbs_div_mod",
    "dec_rewrite_lt_to_le"
  ]),
  ("k_shape_32", #[
    "assert_return_head_is_parent",
    "caddr_is_peer",
    "canon_member_ci",
    "check_eq_type",
    "check_muts_member_at",
    "const_idxs_rules",
    "flat_find_matching",
    "get_quotient",
    "put_univ_list",
    "get_address_list",
    "get_all_telescope",
    "get_expr_list",
    "get_lam_telescope",
    "collect_index_doms",
    "compute_iprj_addr",
    "k_is_def_eq_core"
  ]),
  ("k_shape_33", #[
    "bitvec_prep_spine",
    "build_rule_rhs"
  ]),
  ("k_shape_34", #[
    "addr_set_build",
    "struct_is_rec",
    "convert_rec_rules",
    "run_check_env",
    "collect_n_doms_whnf",
    "convert_univ_idxs",
    "is_rec_field_peel",
    "klimbs_mul_outer",
    "try_def_eq_nat",
    "peel_ctor_params_subst",
    "validate_univ_params_seen"
  ]),
  ("k_shape_35", #[
    "bitvec_prep_spine_ult",
    "ctx_seek_cut",
    "normalize_int_dec_rebuild",
    "canon_cmp_u64_lex",
    "u64_add",
    "u64_sub_with_borrow"
  ]),
  ("k_shape_36", #[
    "flat_find_pos_kind",
    "canon_cmp_krec_rule_list_ctx",
    "check_valid_ind_app",
    "level_max",
    "subst_param_for",
    "try_match_nat_add",
    "check_inductive_shape_ctors",
    "ctor_subst_param_for",
    "ctx_close_cut"
  ]),
  ("k_shape_37", #[
    "get_definition",
    "populate_rules",
    "char_lit_codepoint_syn",
    "try_def_eq_app",
    "level_max_offsets",
    "nl_eq",
    "try_k_synth_iota"
  ]),
  ("k_shape_38", #[
    "univ_succ_base",
    "struct_scan_ctors",
    "build_minor_doms"
  ]),
  ("k_shape_39", #[
    "cleanup_nat_offset_major",
    "nlvars_any_offset_geq",
    "nlvars_dominates",
    "nlvars_max_offset",
    "ctx_trim",
    "is_dec_prim_addr",
    "is_native_prim_addr",
    "try_nat_offset_dispatch"
  ]),
  ("k_shape_40", #[
    "bytes_to_u64_limb",
    "list_length_u64.Ptr.Univ",
    "build_rec_type",
    "build_succ_chain"
  ]),
  ("k_shape_41", #[
    "check_nested_ctors_positivity",
    "try_extract_int",
    "k_is_def_eq_slow2",
    "check_const"
  ]),
  ("k_shape_42", #[
    "get_constructor_proj",
    "put_recursor_rule"
  ]),
  ("k_shape_43", #[
    "expr_addr",
    "put_axiom",
    "put_quotient",
    "get_u64_list",
    "put_univ",
    "delta_unfold"
  ]),
  ("k_shape_44", #[
    "nl_add_const_go",
    "try_quot_ind",
    "try_quot_lift",
    "walk_char_list_bytes",
    "is_str_prim_addr"
  ]),
  ("k_shape_45", #[
    "get_tag0",
    "get_tag2",
    "klimbs_eq",
    "klimbs_succ",
    "collect_spine_of_ctor",
    "whnf_nd_const_head",
    "compute_k_target",
    "canon_cprj_addr"
  ]),
  ("k_shape_46", #[
    "nat_offset_of",
    "projection_addr_ctor",
    "projection_definition_info",
    "canon_cmp_ctor_pair_ctx",
    "try_bitvec_dispatch"
  ]),
  ("k_shape_47", #[
    "ctors_before_pos",
    "put_expr_list",
    "build_flat_own_params",
    "canon_cmp_klimbs_tail",
    "get_recursor_rule_list",
    "get_univ_list",
    "build_all_minors_walk",
    "build_all_motives_walk",
    "lazy_delta_a_const_b_proj",
    "lazy_delta_b_const_a_proj",
    "whnf_iota_major"
  ]),
  ("k_shape_48", #[
    "nl_covers_const",
    "canon_build_ctx_members",
    "check_recursor_member",
    "try_nat_binop_dispatch",
    "try_reduce_bit_vec_ult",
    "build_ih_doms"
  ]),
  ("k_shape_49", #[
    "klimbs_normalize",
    "put_constructor"
  ]),
  ("k_shape_50", #[
    "is_nat_succ_ih_step",
    "try_normalize_int_decidable",
    "try_reduce_subtype_val",
    "try_str_to_byte_array",
    "try_dec_dispatch"
  ]),
  ("k_shape_51", #[
    "try_nat_linear_rec",
    "try_str_back"
  ]),
  ("k_shape_52", #[
    "rbtree_map_lookup_or_default.G",
    "whnf_nd_proj_head",
    "whnf_proj_head",
    "bytes_to_limbs",
    "has_bvar_in_range",
    "try_str_dec_eq",
    "try_reduce_size_of_unit"
  ]),
  ("k_shape_53", #[
    "build_rec_type_from",
    "k_synth_gate",
    "dec_build_proof",
    "apply_ihs_full"
  ]),
  ("k_shape_54", #[
    "klimbs_land",
    "klimbs_lor",
    "klimbs_xor_op"
  ]),
  ("k_shape_55", #[
    "str_lit_delta_step",
    "glist_ordered_insert",
    "try_nat_dispatch_prewhnf"
  ]),
  ("k_shape_56", #[
    "glist_cmp",
    "glist_subset",
    "utf8_decode_one",
    "dec_finish"
  ]),
  ("k_shape_57", #[
    "verify_bytes_against",
    "get_univ"
  ]),
  ("k_shape_58", #[
    "canon_insert_sorted",
    "bytes_to_addr",
    "is_unit_like_type"
  ]),
  ("k_shape_59", #[
    "canon_cmp_ctor_range_ctx",
    "put_inductive"
  ]),
  ("k_shape_60", #[
    "all_telescope_count",
    "app_telescope_count",
    "lam_telescope_count",
    "check_ctor_entry"
  ]),
  ("k_shape_61", #[
    "canon_group_walk",
    "check_positivity_aug"
  ]),
  ("k_shape_62", #[
    "put_recursor",
    "canon_cmp_member_same_kind_ctx",
    "try_native_dispatch"
  ]),
  ("k_shape_63", #[
    "count_ctors",
    "put_constructor_list",
    "put_all_telescope",
    "put_app_telescope",
    "put_lam_telescope",
    "check_recr_rules"
  ]),
  ("k_shape_64", #[
    "try_lazy_delta_app",
    "rbtree_map_ins.G",
    "k_infer_proj",
    "try_struct_eta_iota"
  ]),
  ("k_shape_65", #[
    "klimbs_add_carry",
    "get_constructor",
    "klimbs_sub_borrow",
    "put_definition"
  ]),
  ("k_shape_66", #[
    "str_dec_eq_build",
    "nlvars_add",
    "try_nat_binop_addr"
  ]),
  ("k_shape_67", #[
    "get_mut_const",
    "check_muts_all",
    "get_constructor_list"
  ]),
  ("k_shape_68", #[
    "try_eta_struct",
    "run_reveal"
  ]),
  ("k_shape_69", #[
    "is_muts_block",
    "detect_aux_from_recrs_ex",
    "find_peer_recursor_with_spec",
    "muts_indc_count_is_one",
    "canon_indc_positions",
    "put_mut_const_list"
  ]),
  ("k_shape_70", #[
    "canon_muts_has_kind",
    "get_ctor_entry",
    "check_ctor_entries",
    "build_recur_addrs_walk"
  ]),
  ("k_shape_71", #[
    "check_block_peer_param_agreement",
    "ind_is_solo",
    "struct_block_member_addrs",
    "list_length_u64.Constructor",
    "const_idxs_muts"
  ]),
  ("k_shape_72", #[
    "run_check_transitive",
    "env_walk"
  ]),
  ("k_shape_73", #[
    "get_mut_const_list",
    "put_expr"
  ]),
  ("k_shape_74", #[
    "prim_family",
    "lazy_delta_step_const_const"
  ]),
  ("k_shape_75", #[
    "check_opt_addr",
    "get_mut_entry"
  ]),
  ("k_shape_76", #[
    "address_eq_tail",
    "address_eq",
    "check_opt_expr_addr",
    "get_ci"
  ]),
  ("k_shape_77", #[
    "flat_originals_walk",
    "get_recursor",
    "peer_agree_walk",
    "run_claim"
  ]),
  ("k_shape_78", #[
    "try_reduce_decide_bitvec_lt",
    "check_canonical_block"
  ]),
  ("k_shape_79", #[
    "get_mut_entry_list_inner",
    "first_recr_parent_block",
    "list_lookup_u64.Constructor"
  ]),
  ("k_shape_80", #[
    "load_assumption_tree",
    "find_peer_rec_spec_walk"
  ]),
  ("k_shape_81", #[
    "aux_from_recrs_walk_ex",
    "get_reveal_info",
    "get_reveal_mut_const_info"
  ]),
  ("k_shape_82", #[
    "get_address",
    "utf8_encode_prepend"
  ]),
  ("k_shape_83", #[
    "list_lookup_u64.MutConst",
    "projection_addr",
    "get_ci_iprj",
    "get_ci_rprj",
    "get_ci_dprj",
    "check_muts_components"
  ]),
  ("k_shape_84", #[
    "blake3_next_layer",
    "get_constant",
    "get_ci_cprj",
    "blake3_finish"
  ])
]

end IxVM

end
