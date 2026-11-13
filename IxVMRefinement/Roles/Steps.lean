import IxVMRefinement.Roles.Tables
import IxVMRefinement.Roles.Lookups

/-! # The `Roles` family's steps

`roles_step c hc`: the registry's `Steps` restricted to the `Roles` family
(`Core/Specs/Roles.lean`): every function of `KernelRoles`, `KernelRoleSpec` and `RBTreeMap` in
`Specs.Roles.Fn` meets its registered spec, from the induction hypothesis at its derivation's
calls. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

/-- **One step per function of the `Roles` family.** -/
theorem roles_step (c : Ctx) (hc : CoreFacts c) :
    ∀ (f : Specs.Roles.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.roles f).name args h r h' cs → IH c cs →
      (Fn.roles f).spec c args h r h' cs
  | .role_map_lookup_or_default_addr, _, _, _, _, _, ev, _ =>
    role_map_lookup_or_default_addr_step c ev
  | .role_map_lookup_or_default_evidence, _, _, _, _, _, ev, _ =>
    role_map_lookup_or_default_evidence_step c ev
  | .rbtree_map_lookup_or_default_field, _, _, _, _, _, ev, _ =>
    rbtree_map_lookup_or_default_field_step c ev
  | .role_ctx_table, _, _, _, _, _, ev, _ => role_ctx_table_step c ev
  | .role_addr_index, _, _, _, _, _, ev, _ => role_addr_index_step c ev
  | .role_bound_addr_or_zero, _, _, _, _, _, ev, _ => role_bound_addr_or_zero_step c ev
  | .role_is_bound, _, _, _, _, _, ev, ih => role_is_bound_step c ev ih
  | .role_bound_addr, _, _, _, _, _, ev, ih => role_bound_addr_step c ev ih
  | .role_index_of, _, _, _, _, _, ev, ih => role_index_of_step c ev ih
  | .role_of, _, _, _, _, _, ev, ih => role_of_step c ev ih
  | .role_is, _, _, _, _, _, ev, ih => role_is_step c hc ev ih
  | .role_addr, _, _, _, _, _, ev, ih => role_addr_step c ev ih
  | .role_used_implicitly, _, _, _, _, _, ev, ih => role_used_implicitly_step c ev ih
  | .role_evidence, _, _, _, _, _, ev, _ => role_evidence_step c ev
  | .role_nat, _, _, _, _, _, ev, _ => role_nat_step c ev
  | .role_nat_zero, _, _, _, _, _, ev, _ => role_nat_zero_step c ev
  | .role_nat_succ, _, _, _, _, _, ev, _ => role_nat_succ_step c ev
  | .role_nat_add, _, _, _, _, _, ev, _ => role_nat_add_step c ev
  | .role_bool_true, _, _, _, _, _, ev, _ => role_bool_true_step c ev
  | .role_bool_false, _, _, _, _, _, ev, _ => role_bool_false_step c ev
  | .role_char, _, _, _, _, _, ev, _ => role_char_step c ev
  | .role_char_of_nat, _, _, _, _, _, ev, _ => role_char_of_nat_step c ev
  | .role_list_nil, _, _, _, _, _, ev, _ => role_list_nil_step c ev
  | .role_list_cons, _, _, _, _, _, ev, _ => role_list_cons_step c ev
  | .role_string, _, _, _, _, _, ev, _ => role_string_step c ev
  | .role_string_of_list, _, _, _, _, _, ev, _ => role_string_of_list_step c ev
  | .role_quot_mk, _, _, _, _, _, ev, _ => role_quot_mk_step c ev
  | .role_quot_lift, _, _, _, _, _, ev, _ => role_quot_lift_step c ev
  | .role_quot_ind, _, _, _, _, _, ev, _ => role_quot_ind_step c ev
  | .role_prim_family, _, _, _, _, _, ev, _ => role_prim_family_step c ev

end IxVM.Refinement.Core
