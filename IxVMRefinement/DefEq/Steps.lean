import IxVMRefinement.DefEq.Delta
import IxVMRefinement.DefEq.Tiers
import IxVMRefinement.DefEq.Offsets
import IxVMRefinement.DefEq.Rescue
import IxVMRefinement.DefEq.ProofIrrel

/-! # The `DefEq` family's steps

`defEq_step c hc`: the registry's `Steps` restricted to the `DefEq` family (`Core/Specs/DefEq.lean`):
every function of `KernelDefEq` meets its registered spec, from the induction hypothesis at its
derivation's calls. The step lemmas are in `Core/Steps/DefEq.lean` (the ordered tiers' entry and
spine congruence) and `DefEq/{Delta,Tiers,Offsets,Rescue,ProofIrrel}.lean`; those that read the
role table, the environment or the loads take the context's facts (`CoreFacts c`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

/-- **The step of one function of the family**: its spec, for every observed derivation, from the
induction hypothesis at the derivation's calls. -/
def DefEqStepAt (c : Ctx) (f : Specs.DefEq.Fn) : Prop :=
  ∀ (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
    (cs : List (Call F)), ObsFn W (Fn.defEq f).name args h r h' cs → IH c cs →
      (Fn.defEq f).spec c args h r h' cs

/-- **One step per function of the `DefEq` family.** -/
theorem defEq_step (c : Ctx) (hc : CoreFacts c) :
    ∀ (f : Specs.DefEq.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.defEq f).name args h r h' cs → IH c cs →
      (Fn.defEq f).spec c args h r h' cs
  | .compare_struct_fields, _, _, _, _, _, ev, ih => compare_struct_fields_step c ev ih
  | .compute_iprj_addr, _, _, _, _, _, ev, ih => compute_iprj_addr_step c hc ev ih
  | .de_args, _, _, _, _, _, ev, ih => de_args_step c ev ih
  | .de_binder, _, _, _, _, _, ev, ih => de_binder_step c ev ih
  | .de_proj, _, _, _, _, _, ev, ih => de_proj_step c ev ih
  | .de_rescue_tier, _, _, _, _, _, ev, ih => de_rescue_tier_step c ev ih
  | .delta_rank, _, _, _, _, _, ev, ih => delta_rank_step c ev ih
  | .delta_unfold, _, _, _, _, _, ev, ih => delta_unfold_step c hc ev ih
  | .family_params, _, _, _, _, _, ev, ih => family_params_step c ev ih
  | .head_addr, _, _, _, _, _, ev, ih => head_addr_step c ev ih
  | .is_defn_or_thm, _, _, _, _, _, ev, ih => is_defn_or_thm_step c ev ih
  | .is_nat_zero, _, _, _, _, _, ev, ih => is_nat_zero_step c hc ev ih
  | .is_prop_type, _, _, _, _, _, ev, ih => is_prop_type_step c ev ih
  | .is_unit_like_type, _, _, _, _, _, ev, ih => is_unit_like_type_step c hc ev ih
  | .k_def_eq_rebase, _, _, _, _, _, ev, ih => k_def_eq_rebase_step c hc ev ih
  | .k_is_def_eq, _, _, _, _, _, ev, ih => k_is_def_eq_step c ev ih
  | .k_is_def_eq_core, _, _, _, _, _, ev, ih => k_is_def_eq_core_step c ev ih
  | .k_is_def_eq_ordered, _, _, _, _, _, ev, ih => k_is_def_eq_ordered_step c ev ih
  | .k_is_def_eq_slow, _, _, _, _, _, ev, ih => k_is_def_eq_slow_step c ev ih
  | .k_is_def_eq_slow2, _, _, _, _, _, ev, ih => k_is_def_eq_slow2_step c ev ih
  | .k_is_def_eq_slow_nd, _, _, _, _, _, ev, ih => k_is_def_eq_slow_nd_step c ev ih
  | .k_is_def_eq_slow_nd_after_core, _, _, _, _, _, ev, ih =>
    k_is_def_eq_slow_nd_after_core_step c ev ih
  | .k_is_def_eq_struct, _, _, _, _, _, ev, ih => k_is_def_eq_struct_step c ev ih
  | .k_is_def_eq_struct_bounded, _, _, _, _, _, ev, ih => k_is_def_eq_struct_bounded_step c ev ih
  | .k_is_def_eq_struct_go, _, _, _, _, _, ev, ih => k_is_def_eq_struct_go_step c ev ih
  | .k_is_def_eq_struct_safe, _, _, _, _, _, ev, ih => k_is_def_eq_struct_safe_step c ev ih
  | .k_is_def_eq_struct_spend, _, _, _, _, _, ev, ih => k_is_def_eq_struct_spend_step c ev ih
  | .k_is_def_eq_structure_tree, _, _, _, _, _, ev, ih => k_is_def_eq_structure_tree_step c ev ih
  | .k_is_def_eq_structure_tree_app, _, _, _, _, _, ev, ih =>
    k_is_def_eq_structure_tree_app_step c ev ih
  | .lazy_delta_a_const_b_proj, _, _, _, _, _, ev, ih => lazy_delta_a_const_b_proj_step c ev ih
  | .lazy_delta_b_const_a_proj, _, _, _, _, _, ev, ih => lazy_delta_b_const_a_proj_step c ev ih
  | .lazy_delta_both_proj, _, _, _, _, _, ev, ih => lazy_delta_both_proj_step c ev ih
  | .lazy_delta_loop, _, _, _, _, _, ev, ih => lazy_delta_loop_step c ev ih
  | .lazy_delta_step_const_const, _, _, _, _, _, ev, ih =>
    lazy_delta_step_const_const_step c ev ih
  | .leading_foralls, _, _, _, _, _, ev, ih => leading_foralls_step c ev ih
  | .level_list_eq, _, _, _, _, _, ev, ih => level_list_eq_step c ev ih
  | .nat_offset_of, _, _, _, _, _, ev, ih => nat_offset_of_step c hc ev ih
  | .slow2_after_delta, _, _, _, _, _, ev, ih => slow2_after_delta_step c ev ih
  | .slow2_eager_fallback, _, _, _, _, _, ev, ih => slow2_eager_fallback_step c ev ih
  | .try_def_eq_app, _, _, _, _, _, ev, ih => try_def_eq_app_step c ev ih
  | .try_def_eq_nat, _, _, _, _, _, ev, ih => try_def_eq_nat_step c hc ev ih
  | .try_eta_expand, _, _, _, _, _, ev, ih => try_eta_expand_step c ev ih
  | .try_eta_struct, _, _, _, _, _, ev, ih => try_eta_struct_step c hc ev ih
  | .try_eta_swap, _, _, _, _, _, ev, ih => try_eta_swap_step c ev ih
  | .try_lazy_delta_app, _, _, _, _, _, ev, ih => try_lazy_delta_app_step c ev ih
  | .try_proof_irrel, _, _, _, _, _, ev, ih => try_proof_irrel_step c hc ev ih
  | .try_same_proj_head_app, _, _, _, _, _, ev, ih => try_same_proj_head_app_step c ev ih
  | .try_string_lit_one, _, _, _, _, _, ev, ih => try_string_lit_one_step c ev ih
  | .try_string_lit_pair, _, _, _, _, _, ev, ih => try_string_lit_pair_step c ev ih
  | .try_unfold_head, _, _, _, _, _, ev, ih => try_unfold_head_step c ev ih
  | .try_unfold_proj_app, _, _, _, _, _, ev, ih => try_unfold_proj_app_step c ev ih
  | .try_unit_like, _, _, _, _, _, ev, ih => try_unit_like_step c ev ih
  | .unfold_a_and_loop, _, _, _, _, _, ev, ih => unfold_a_and_loop_step c ev ih
  | .unfold_b_and_loop, _, _, _, _, _, ev, ih => unfold_b_and_loop_step c ev ih
  | .unfold_both_and_loop, _, _, _, _, _, ev, ih => unfold_both_and_loop_step c ev ih

end IxVM.Refinement.Core
