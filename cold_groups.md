# Proposed cold circuit groups

Data: main-branch per-circuit stats from `ix check` on `Nat.add_comm`
(`nat_add_comm_result`) and `String.append` (`string_append_result`).

- **calls** = trace height + cache hits, summed over all monomorphized
  instances of a source function.
- **cold** = fewer than 100 calls in *both* workloads. 468 of 719
  non-`pub` functions qualify (140 functions that looked cold on
  `Nat.add_comm` alone are hot on `String.append` and stay ungrouped).
- **width** = max singleton circuit width over the function's instances.
- Groups are width bands, so members of a group waste little of the
  merged circuit's shared (max-sized) column region.

## Summary

| group | width band | members | Σ max-calls | calls nat | calls str |
|-------|-----------:|--------:|------------:|----------:|----------:|
| cold1 | [0, 16) | 62 | 211 | 62 | 210 |
| cold2 | [16, 24) | 88 | 1930 | 447 | 1930 |
| cold3 | [24, 32) | 89 | 1998 | 453 | 1998 |
| cold4 | [32, 48) | 87 | 1750 | 382 | 1750 |
| cold5 | [48, 64) | 44 | 868 | 215 | 868 |
| cold6 | [64, 96) | 65 | 979 | 252 | 978 |
| cold7 | [96, ∞) | 33 | 426 | 118 | 426 |

## cold1 — width [0, 16), 62 members

| function | width | calls (Nat.add_comm) | calls (String.append) |
|----------|------:|---------------------:|----------------------:|
| sentinel_blob_ref | 6 | 2 | 19 |
| sord_eq_strong | 6 | 0 | 0 |
| sord_gt_strong | 6 | 0 | 0 |
| sord_lt_strong | 6 | 0 | 0 |
| sord_of_g | 7 | 0 | 0 |
| bit_vec_addr | 9 | 1 | 1 |
| bool_type_addr | 9 | 1 | 1 |
| byte_array_empty_addr | 9 | 1 | 1 |
| char_of_nat_addr | 9 | 1 | 1 |
| char_type_addr | 9 | 1 | 1 |
| decidable_is_false_addr | 9 | 1 | 1 |
| decidable_is_true_addr | 9 | 1 | 1 |
| decidable_rec_addr | 9 | 1 | 1 |
| def_safety_tag | 9 | 0 | 0 |
| eq_addr | 9 | 1 | 1 |
| eq_refl_addr | 9 | 1 | 1 |
| list_cons_addr | 9 | 1 | 1 |
| list_nil_addr | 9 | 1 | 1 |
| lt_lt_addr | 9 | 1 | 1 |
| nat_addr | 9 | 2 | 2 |
| nat_eq_of_beq_eq_true_addr | 9 | 1 | 1 |
| nat_le_of_ble_eq_true_addr | 9 | 1 | 1 |
| nat_ne_of_beq_eq_false_addr | 9 | 1 | 1 |
| nat_not_le_of_not_ble_eq_true_addr | 9 | 1 | 1 |
| nat_zero_addr | 9 | 4 | 8 |
| quot_ctor_addr | 9 | 1 | 1 |
| quot_ind_addr | 9 | 1 | 1 |
| quot_lift_addr | 9 | 1 | 1 |
| quot_type_addr | 9 | 1 | 1 |
| str_addr | 9 | 1 | 1 |
| string_of_list_addr | 9 | 1 | 1 |
| check_opt_bool | 10 | 0 | 0 |
| mk_nat_lit | 10 | 3 | 20 |
| ord_then | 10 | 0 | 0 |
| quot_kind_tag | 10 | 0 | 0 |
| run_eval | 10 | 0 | 0 |
| utf8_last_codepoint | 10 | 0 | 0 |
| inductive_ctor_count_at | 11 | 7 | 30 |
| klimbs_add | 11 | 1 | 0 |
| augment_block_idxs | 12 | 0 | 0 |
| build_recur_idxs | 12 | 7 | 30 |
| build_rule_ctor_idxs | 12 | 0 | 0 |
| check_opt_ctor_entries | 12 | 0 | 0 |
| check_opt_recr_rules | 12 | 0 | 0 |
| extract_member_ctor_idxs | 12 | 2 | 14 |
| klimbs_div | 12 | 0 | 0 |
| klimbs_mod | 12 | 0 | 0 |
| sord_then | 12 | 0 | 0 |
| synth_aux_ind_ty | 12 | 0 | 0 |
| check_all | 13 | 1 | 1 |
| get_opt_addr_masked | 14 | 0 | 0 |
| get_opt_bool_masked | 14 | 0 | 0 |
| ind_has_nested | 14 | 2 | 14 |
| klimbs_mul | 14 | 0 | 0 |
| put_quot_kind | 14 | 0 | 0 |
| run_contains | 14 | 0 | 0 |
| build_flat_block | 15 | 4 | 28 |
| check_canonical_block_sort | 15 | 1 | 1 |
| compare_kuniv_list_sord | 15 | 0 | 0 |
| mk_nat_literal_64 | 15 | 0 | 0 |
| mk_nat_one | 15 | 0 | 0 |
| peel_rule_ctor_params | 15 | 3 | 20 |

## cold2 — width [16, 24), 88 members

| function | width | calls (Nat.add_comm) | calls (String.append) |
|----------|------:|---------------------:|----------------------:|
| build_all_motives | 16 | 4 | 28 |
| build_block_start_map | 16 | 1 | 1 |
| build_major_args_for_member | 16 | 2 | 14 |
| check_opt_def_safety | 16 | 0 | 0 |
| check_opt_quot_kind | 16 | 0 | 0 |
| check_param_agreement | 16 | 16 | 72 |
| compare_kliteral | 16 | 0 | 0 |
| get_opt_addr | 16 | 1 | 1 |
| get_opt_def_kind_masked | 16 | 0 | 0 |
| klimbs_dec | 16 | 5 | 13 |
| klimbs_shl_limbs | 16 | 0 | 0 |
| klimbs_sub | 16 | 3 | 4 |
| list_repeat_stub | 16 | 70 | 70 |
| literal_eq | 16 | 0 | 0 |
| pack_def_kind_safety | 16 | 0 | 0 |
| build_ctor_app_params | 17 | 3 | 20 |
| build_ctor_idxs | 17 | 17 | 80 |
| build_major_args_for_self | 17 | 2 | 14 |
| canonicalize_pos_map | 17 | 1 | 1 |
| get_opt_quot_kind_masked | 17 | 0 | 0 |
| has_bvar_in_range_binder | 17 | 0 | 0 |
| peel_leading_foralls | 17 | 10 | 84 |
| sort_kconsts | 17 | 0 | 0 |
| validate_block_auxes | 17 | 7 | 30 |
| collect_n_doms | 18 | 13 | 72 |
| ensure_sort_post_whnf | 18 | 2 | 6 |
| klimbs_gcd | 18 | 0 | 0 |
| try_quot_iota | 18 | 0 | 0 |
| build_pos_map | 19 | 1 | 1 |
| build_rec_lvls | 19 | 6 | 23 |
| check_native_nat | 19 | 0 | 0 |
| find_rec_for_ind | 19 | 2 | 14 |
| flatten_classes | 19 | 0 | 0 |
| leaf_hash | 19 | 0 | 0 |
| nat_const_type | 19 | 3 | 20 |
| run_check | 19 | 1 | 1 |
| skip_bytes | 19 | 4 | 47 |
| str_const_type | 19 | 0 | 0 |
| all_singleton_classes | 20 | 0 | 0 |
| apply_indices_in_conclusion | 20 | 3 | 20 |
| build_all_minors | 20 | 4 | 28 |
| build_apply_xs | 20 | 8 | 48 |
| build_param_lvls_range | 20 | 5 | 29 |
| compute_layout | 20 | 1 | 1 |
| ctx_class_idx | 20 | 0 | 0 |
| klimbs_shl | 20 | 0 | 0 |
| klimbs_shr | 20 | 0 | 0 |
| list_reverse_acc | 20 | 31 | 97 |
| nl_add_const | 20 | 9 | 18 |
| put_address_list | 20 | 1 | 1 |
| all_bvars_in_args | 21 | 0 | 2 |
| build_apply_field_bvars | 21 | 8 | 67 |
| build_apply_minors | 21 | 15 | 99 |
| build_major_params | 21 | 4 | 29 |
| check_field_universes | 21 | 16 | 72 |
| check_positivity | 21 | 16 | 72 |
| count_foralls_at_least | 21 | 0 | 0 |
| get_opt_u64_masked | 21 | 0 | 0 |
| init_block_members | 21 | 14 | 73 |
| insertion_sort_class | 21 | 0 | 0 |
| list_any_mentions | 21 | 9 | 68 |
| lookup_addr_pos | 21 | 7 | 30 |
| member_has_nested | 21 | 14 | 60 |
| spec_params_valid | 21 | 0 | 0 |
| utf8_last_go | 21 | 0 | 0 |
| validate_recr_rules | 21 | 5 | 34 |
| addr_in_list | 22 | 0 | 0 |
| any_member_has_nested | 22 | 16 | 74 |
| apply_n_projs | 22 | 0 | 2 |
| build_canon_addr_map | 22 | 1 | 1 |
| check_all_skipping | 22 | 0 | 0 |
| check_block_peer_param_agreement | 22 | 7 | 30 |
| check_prop_field_if_prop | 22 | 8 | 62 |
| collect_index_doms | 22 | 3 | 20 |
| flat_ind_idxs | 22 | 6 | 42 |
| get_inductive_proj | 22 | 7 | 30 |
| has_bvar_in_range_let | 22 | 0 | 0 |
| peel_leading_foralls_acc | 22 | 8 | 56 |
| put_definition_proj | 22 | 0 | 0 |
| refine_one_class | 22 | 0 | 0 |
| resolve_primary_ind_for_rec | 22 | 2 | 14 |
| run_check_env | 22 | 0 | 0 |
| scan_fields_for_block_ref | 22 | 0 | 13 |
| assert_lvls_are_params | 23 | 14 | 41 |
| nl_subsumption_walk | 23 | 27 | 44 |
| node_hash | 23 | 0 | 0 |
| relaxed_u64_succ | 23 | 0 | 15 |
| spec_params_lower | 23 | 4 | 22 |

## cold3 — width [24, 32), 89 members

| function | width | calls (Nat.add_comm) | calls (String.append) |
|----------|------:|---------------------:|----------------------:|
| apply_spec_params_lifted | 24 | 0 | 0 |
| check_opt_u64 | 24 | 0 | 0 |
| collect_n_doms_acc | 24 | 22 | 57 |
| glist_eq_len | 24 | 27 | 38 |
| group_consecutive_class | 24 | 0 | 0 |
| ingress_with_primitives | 24 | 1 | 1 |
| kconst_kind_ord | 24 | 15 | 66 |
| klimbs_is_zero | 24 | 13 | 23 |
| list_lift_each | 24 | 4 | 27 |
| list_lift_indices | 24 | 7 | 57 |
| put_refs | 24 | 8 | 36 |
| put_sharing | 24 | 8 | 36 |
| put_u64_le | 24 | 0 | 0 |
| put_univs | 24 | 8 | 36 |
| refine_classes | 24 | 0 | 0 |
| synthetic_primitive_entries | 24 | 1 | 1 |
| unfold_a_and_loop | 24 | 0 | 0 |
| unfold_b_and_loop | 24 | 0 | 0 |
| addr_in_set | 25 | 0 | 0 |
| assert_first_args_are_param_bvars | 25 | 18 | 55 |
| build_addr_tree | 25 | 1 | 1 |
| check_field_universes_skip_params | 25 | 15 | 42 |
| check_positivity_fields_aug | 25 | 14 | 73 |
| compare_kexpr | 25 | 0 | 0 |
| ctx_cmp_idx | 25 | 0 | 0 |
| first_pos_for_mptr | 25 | 0 | 0 |
| g_list_eq | 25 | 0 | 0 |
| get_opt_ctor_entry_list_masked | 25 | 0 | 0 |
| get_opt_rule_list_masked | 25 | 0 | 0 |
| klimbs_le | 25 | 0 | 1 |
| level_reduce | 25 | 31 | 43 |
| peel_n_foralls_with_types | 25 | 18 | 73 |
| sort_kconsts_loop | 25 | 0 | 0 |
| spec_params_ptr_eq | 25 | 0 | 0 |
| validate_block_if_nonzero | 25 | 15 | 74 |
| args_contain_bvar | 26 | 0 | 2 |
| ctor_num_params_of | 26 | 6 | 40 |
| delta_rank | 26 | 0 | 0 |
| detect_nested_in_field_chain | 26 | 17 | 94 |
| nl_le_vars | 26 | 13 | 18 |
| check_large_prop_ctor | 27 | 0 | 5 |
| compare_kexpr_ctx | 27 | 0 | 0 |
| compare_klimbs | 27 | 0 | 0 |
| convert_axiom | 27 | 0 | 1 |
| convert_quotient | 27 | 0 | 0 |
| expr_lbr_let | 27 | 1 | 22 |
| flat_member_at | 27 | 8 | 56 |
| ingress_env | 27 | 0 | 0 |
| put_u64_list | 27 | 0 | 0 |
| synth_aux_subst | 27 | 0 | 0 |
| try_eta_expand | 27 | 0 | 3 |
| check_no_dep_data_field_if_prop | 28 | 0 | 12 |
| gather_block_nested | 28 | 14 | 60 |
| is_delta_eligible | 28 | 0 | 62 |
| k_ensure_sort_only | 28 | 0 | 92 |
| level_leq | 28 | 6 | 24 |
| put_recursor_rule_list | 28 | 0 | 0 |
| try_str_to_byte_array | 28 | 0 | 0 |
| build_ctor_pairs_computed | 29 | 15 | 66 |
| check_field_universes_inner | 29 | 13 | 47 |
| check_quot | 29 | 0 | 0 |
| classes_eq | 29 | 0 | 0 |
| klimbs_from_g | 29 | 0 | 0 |
| lookup_canon_addr | 29 | 7 | 30 |
| parse_atree_body | 29 | 0 | 0 |
| peel_motive_params_subst | 29 | 4 | 26 |
| compare_byte_stream | 30 | 0 | 0 |
| compare_kuniv_list | 30 | 0 | 0 |
| compare_struct_fields | 30 | 0 | 12 |
| detect_nested_in_orig | 30 | 14 | 60 |
| find_flat_member_match | 30 | 2 | 36 |
| lazy_delta_step_a_const | 30 | 0 | 4 |
| lazy_delta_step_b_const | 30 | 0 | 6 |
| peel_ctor_params_subst | 30 | 5 | 42 |
| put_tag0 | 30 | 19 | 75 |
| try_const_app_congruence | 30 | 1 | 68 |
| try_unfold_proj_app | 30 | 0 | 0 |
| validate_block_canonical | 30 | 7 | 29 |
| check_inductive_shape | 31 | 9 | 44 |
| computed_is_rec_ind | 31 | 0 | 12 |
| is_inductive_prop | 31 | 8 | 62 |
| level_normalize | 31 | 14 | 30 |
| mk_bool | 31 | 0 | 4 |
| normalize_aux | 31 | 32 | 68 |
| put_tag2 | 31 | 0 | 0 |
| put_tag4 | 31 | 8 | 36 |
| put_univ_list | 31 | 1 | 1 |
| spine_prefix_eq | 31 | 2 | 8 |
| u64_eq | 31 | 1 | 1 |

## cold4 — width [32, 48), 87 members

| function | width | calls (Nat.add_comm) | calls (String.append) |
|----------|------:|---------------------:|----------------------:|
| klimbs_div_mod | 32 | 0 | 0 |
| rec_declared_spec | 32 | 2 | 14 |
| unfold_both_and_loop | 32 | 0 | 0 |
| compare_rules | 33 | 5 | 34 |
| detect_nested_in_member | 33 | 2 | 14 |
| flat_append_new_auxes | 33 | 2 | 14 |
| get_constructor_proj | 33 | 8 | 34 |
| intern_int_lit | 33 | 0 | 0 |
| nl_covers_var | 33 | 14 | 19 |
| put_constructor_proj | 33 | 8 | 36 |
| check_native_bool | 34 | 0 | 0 |
| check_param_agreement_go | 34 | 18 | 73 |
| cprj_content_addr | 34 | 8 | 36 |
| get_tag2 | 34 | 50 | 96 |
| nl_le | 34 | 11 | 15 |
| nlvars_eq | 34 | 0 | 10 |
| peel_field_loop | 34 | 8 | 74 |
| try_str_back | 34 | 0 | 0 |
| ord_cmp_g | 35 | 0 | 0 |
| try_extract_nat_app | 35 | 6 | 66 |
| utf8_decode_one | 35 | 0 | 0 |
| apply_ctor_overrides_tree | 36 | 9 | 37 |
| bytes_to_limbs | 36 | 7 | 83 |
| expr_addr | 36 | 0 | 0 |
| bv_to_nat_via | 37 | 0 | 0 |
| find_rec_self_pos | 37 | 2 | 14 |
| normalize_imax_dispatch | 37 | 0 | 0 |
| build_char_list | 38 | 0 | 0 |
| build_convert_inputs | 38 | 1 | 1 |
| build_skip_set | 38 | 0 | 0 |
| check_ctor_against_inductive_member | 38 | 8 | 36 |
| compare_krec_rule_list_ctx | 38 | 0 | 0 |
| klimbs_mul_outer | 38 | 0 | 0 |
| univ_succ_base | 38 | 0 | 0 |
| compare_krec_rule_ctx | 39 | 0 | 0 |
| klimbs_succ | 39 | 8 | 14 |
| block_param_decls | 40 | 7 | 30 |
| filter_indc_positions | 40 | 22 | 95 |
| klimbs_to_ctor_form | 40 | 1 | 2 |
| put_expr_list | 40 | 1 | 1 |
| addr_key | 41 | 0 | 0 |
| build_block_start_map_walk | 41 | 8 | 31 |
| ctors_before_pos | 41 | 2 | 14 |
| flat_own_params_of | 41 | 6 | 42 |
| klimbs_pow | 41 | 0 | 0 |
| nl_add_var | 41 | 18 | 36 |
| build_motive_type_flat | 42 | 2 | 14 |
| check_ctor_return_type | 42 | 16 | 72 |
| compare_klimbs_tail | 42 | 0 | 0 |
| compare_kuniv | 42 | 0 | 0 |
| expr_lower | 42 | 2 | 8 |
| get_recursor_rule | 42 | 3 | 20 |
| is_aux_inductive | 42 | 21 | 90 |
| klimbs_eq | 42 | 9 | 17 |
| put_recursor_rule | 42 | 0 | 0 |
| compute_is_rec | 43 | 0 | 12 |
| delta_unfold | 43 | 0 | 0 |
| is_rec_field | 43 | 2 | 38 |
| nl_eq | 43 | 4 | 18 |
| validate_auxes_walk | 43 | 14 | 60 |
| bytes_to_addr | 44 | 8 | 36 |
| check_large_walk_fields | 44 | 0 | 6 |
| compare_kconst_ctx | 44 | 0 | 0 |
| convert_rules | 44 | 5 | 34 |
| subst_param_for | 44 | 2 | 12 |
| build_flat_originals | 45 | 4 | 28 |
| check_ctors_positivity | 45 | 0 | 0 |
| check_eq_type | 45 | 0 | 0 |
| detect_nested_in_ctors | 45 | 15 | 66 |
| nlvars_max_offset | 45 | 0 | 0 |
| decidable_dispatch_le_eq | 46 | 0 | 5 |
| get_axiom | 46 | 0 | 1 |
| is_large_eliminator | 46 | 4 | 28 |
| klimbs_normalize | 46 | 8 | 9 |
| load_verified_blob | 46 | 7 | 77 |
| nlvars_any_offset_geq | 46 | 0 | 0 |
| put_axiom | 46 | 0 | 0 |
| put_quotient | 46 | 0 | 0 |
| u64_and | 46 | 0 | 0 |
| u64_or | 46 | 0 | 0 |
| u64_xor_kbits | 46 | 0 | 0 |
| walk_fields_classify | 46 | 8 | 78 |
| build_peer_recs | 47 | 4 | 28 |
| check_all_skipping_iter | 47 | 0 | 0 |
| check_recr_rules | 47 | 0 | 0 |
| ctor_subst_param_for | 47 | 2 | 22 |
| univ_succ_count | 47 | 0 | 0 |

## cold5 — width [48, 64), 44 members

| function | width | calls (Nat.add_comm) | calls (String.append) |
|----------|------:|---------------------:|----------------------:|
| bytes_to_u64_limb | 48 | 4 | 47 |
| get_recursor_rule_list | 48 | 5 | 34 |
| nlvars_dominates | 48 | 10 | 14 |
| get_quotient | 49 | 0 | 0 |
| klimbs_land | 50 | 0 | 0 |
| klimbs_lor | 50 | 0 | 0 |
| klimbs_xor_op | 50 | 0 | 0 |
| quot_extract_arg | 50 | 0 | 0 |
| augment_walk | 51 | 0 | 0 |
| build_succ_chain | 51 | 23 | 42 |
| expr_lower_walk | 51 | 2 | 8 |
| get_univ_list | 51 | 38 | 78 |
| put_univ | 51 | 0 | 0 |
| try_extract_int | 51 | 0 | 0 |
| build_all_motives_walk | 52 | 4 | 28 |
| build_minor_doms | 52 | 5 | 34 |
| convert_inductive | 52 | 7 | 30 |
| put_constructor_list | 53 | 0 | 0 |
| build_flat_block_iter | 54 | 4 | 28 |
| check_inductive_shape_ctors | 55 | 15 | 66 |
| detect_nested_in_member_ctors | 55 | 5 | 34 |
| member_kernel_size | 56 | 16 | 73 |
| nl_add_const_go | 56 | 3 | 6 |
| build_all_minors_walk | 57 | 4 | 28 |
| get_reveal_rule_list_inner | 57 | 0 | 0 |
| normalize_int_dec_rebuild | 57 | 0 | 0 |
| populate_rules | 58 | 5 | 34 |
| try_quot_ind | 58 | 0 | 0 |
| try_quot_lift | 58 | 0 | 0 |
| is_nat_succ_ih_step | 59 | 5 | 24 |
| nl_covers_const | 59 | 1 | 2 |
| get_mut_const | 60 | 7 | 30 |
| insert_sorted | 60 | 0 | 0 |
| put_mut_const | 60 | 0 | 0 |
| convert_constructor | 61 | 8 | 36 |
| expand_ctors | 61 | 15 | 66 |
| get_ctor_entry | 61 | 0 | 0 |
| extract_dedup_mptr | 62 | 21 | 90 |
| members_have_indc | 62 | 0 | 0 |
| put_constant_info | 62 | 8 | 36 |
| try_match_aux | 62 | 0 | 0 |
| try_normalize_int_decidable | 63 | 0 | 0 |
| try_reduce_bit_vec_ult | 63 | 0 | 0 |
| try_reduce_subtype_val | 63 | 0 | 0 |

## cold6 — width [64, 96), 65 members

| function | width | calls (Nat.add_comm) | calls (String.append) |
|----------|------:|---------------------:|----------------------:|
| put_mut_const_list | 64 | 0 | 0 |
| all_telescope_count | 65 | 0 | 0 |
| app_telescope_count | 65 | 0 | 0 |
| build_succ_offset | 65 | 1 | 1 |
| check_ctor_entries | 65 | 0 | 0 |
| inductive_ctor_count_walk | 65 | 7 | 29 |
| klimbs_add_carry | 65 | 1 | 0 |
| lam_telescope_count | 65 | 0 | 0 |
| klimbs_sub_borrow | 66 | 3 | 4 |
| build_recur_idxs_walk | 67 | 14 | 60 |
| compare_u64_lex | 67 | 0 | 0 |
| group_consecutive_walk | 67 | 0 | 0 |
| u64_add | 67 | 0 | 1 |
| u64_sub_with_borrow | 67 | 2 | 2 |
| compute_k_target | 68 | 2 | 14 |
| decidable_dispatch | 68 | 0 | 7 |
| check_positivity_aug | 70 | 6 | 38 |
| compare_kexpr_node | 70 | 0 | 0 |
| try_nat_binop_dispatch | 70 | 17 | 81 |
| try_reduce_size_of_unit | 70 | 0 | 0 |
| glist_ordered_insert | 71 | 7 | 15 |
| build_rule_ctor_idxs_walk | 72 | 0 | 0 |
| compare_aux_ctors | 72 | 0 | 0 |
| put_all_telescope | 72 | 0 | 0 |
| put_app_telescope | 72 | 0 | 0 |
| put_lam_telescope | 72 | 0 | 0 |
| extract_member_ctor_idxs_walk | 73 | 2 | 14 |
| get_constructor_list | 73 | 15 | 66 |
| glist_subset | 73 | 62 | 86 |
| has_bvar_in_range | 73 | 0 | 0 |
| glist_cmp | 74 | 18 | 49 |
| put_definition | 74 | 0 | 0 |
| get_mut_entry | 75 | 0 | 0 |
| flat_contains_aux | 76 | 0 | 0 |
| compare_kexpr_node_ctx | 77 | 0 | 0 |
| list_length_u64 | 77 | 3 | 3 |
| check_opt_addr | 78 | 0 | 0 |
| convert_recursor | 78 | 2 | 14 |
| expand_members | 78 | 14 | 60 |
| get_constructor | 79 | 8 | 36 |
| put_constructor | 79 | 0 | 0 |
| check_opt_expr_addr | 81 | 0 | 0 |
| finish_ingress | 82 | 1 | 1 |
| find_rec_self_pos_walk | 83 | 2 | 14 |
| get_mut_const_list | 84 | 14 | 60 |
| klimbs_mul_single | 84 | 0 | 0 |
| try_reduce_bit_vec_to_nat | 84 | 0 | 0 |
| build_ih_doms | 85 | 4 | 24 |
| put_inductive | 85 | 0 | 0 |
| collect_app_spine_expr_head | 86 | 5 | 35 |
| expand_member | 86 | 7 | 30 |
| get_claim | 86 | 1 | 1 |
| get_reveal_ctor_info | 86 | 0 | 0 |
| kexpr_struct_eq | 86 | 0 | 0 |
| lazy_delta_step_const_const | 86 | 0 | 26 |
| get_expr_let | 87 | 1 | 18 |
| get_ctor_entry_list_inner | 88 | 0 | 0 |
| put_constant | 88 | 8 | 36 |
| peel_n_alls_expr | 89 | 10 | 69 |
| build_rule_rhs | 91 | 3 | 20 |
| decidable_finish | 93 | 0 | 0 |
| get_inductive | 93 | 7 | 30 |
| str_lit_to_ctor | 93 | 0 | 0 |
| build_minor_at_depth | 95 | 3 | 20 |
| rec_typ_to_inductive_addr | 95 | 2 | 14 |

## cold7 — width [96, ∞), 33 members

| function | width | calls (Nat.add_comm) | calls (String.append) |
|----------|------:|---------------------:|----------------------:|
| detect_nested_in_dom | 97 | 6 | 38 |
| try_synth_k_ctor | 97 | 0 | 2 |
| level_cmp_tests | 99 | 0 | 0 |
| bitvec_of_nat_args | 100 | 0 | 0 |
| load_assumption_tree | 100 | 0 | 0 |
| nlvars_add | 100 | 0 | 4 |
| get_mut_entry_list_inner | 102 | 0 | 0 |
| check_ctor_entry | 103 | 0 | 0 |
| apply_ihs | 104 | 4 | 24 |
| load_verified_claim | 107 | 1 | 1 |
| address_eq_tail | 108 | 17 | 81 |
| put_expr | 108 | 0 | 0 |
| put_recursor | 108 | 0 | 0 |
| is_singleton_indc | 109 | 14 | 60 |
| nlvars_subsume | 109 | 0 | 0 |
| decidable_build_proof | 112 | 0 | 0 |
| compare_kconst_same_kind_ctx | 114 | 0 | 0 |
| try_nat_binop_addr | 114 | 1 | 7 |
| build_rec_type | 115 | 2 | 14 |
| get_recursor | 115 | 2 | 14 |
| nl_subsume_entry | 119 | 58 | 84 |
| get_reveal_mut_const_info | 124 | 0 | 0 |
| check_mut_const | 125 | 0 | 0 |
| check_muts_components | 126 | 0 | 0 |
| get_reveal_info | 132 | 0 | 0 |
| run_reveal | 137 | 0 | 0 |
| check_recursor_member | 138 | 2 | 14 |
| put_address | 138 | 8 | 36 |
| try_reduce_decide_bitvec_lt | 167 | 0 | 0 |
| build_aux_recr_ctor_idxs | 198 | 2 | 14 |
| blake3_next_layer | 219 | 0 | 32 |
| u64_mul | 266 | 0 | 0 |
| synthetic_primitive_addrs | 423 | 1 | 1 |
