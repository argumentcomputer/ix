import IxVMRefinement.Whnf.Norm
import IxVMRefinement.Whnf.Scans
import IxVMRefinement.Whnf.Beta
import IxVMRefinement.Whnf.Delta
import IxVMRefinement.Whnf.Proj
import IxVMRefinement.Core.Whnf

/-! # The `Whnf` family's steps

`whnf_family_step c hc hrest`: the registry's `Steps` restricted to the `Whnf` family
(`Core/Specs/Whnf.lean`): every function of `KernelWhnf` meets its registered spec, from the
induction hypothesis at its derivation's calls. The step lemmas are the slice's
(`Core/Whnf.lean`, `Core/Steps/Whnf.lean`) and this package's (`Whnf/{Norm,Scans,Beta,Prim,Heads,
Delta}.lean`). The steps of the functions in `whnfPending` are a hypothesis (`hrest`): the ι, K,
structure-η and quotient functions. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

/-- The functions of the family whose steps `whnf_family_step` takes as a hypothesis. -/
def whnfPending : List Specs.Whnf.Fn :=
  [.red_iota, .iota_cmp, .iota_certs, .find_rule, .try_iota, .whnf_iota_major, .pi_peel,
    .pi_residual, .k_synth_fab, .try_k_synth_iota, .eta_iota_fab, .try_struct_eta_iota,
    .struct_is_rec, .struct_scan_members, .struct_block_member_addrs, .struct_scan_ctors,
    .se_parent_addr, .se_peel_tol, .se_scan_fields, .se_mentions, .se_addr_in, .red_quot,
    .quot_certs, .try_quot_iota, .red_rec]

/-- **One step per function of the `Whnf` family**, given the steps of the functions in
`whnfPending`. -/
theorem whnf_family_step (c : Ctx) (hc : CoreFacts c)
    (hrest : ∀ f ∈ whnfPending, ∀ (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.whnf f).name args h r h' cs → IH c cs →
        (Fn.whnf f).spec c args h r h' cs) :
    ∀ (f : Specs.Whnf.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.whnf f).name args h r h' cs → IH c cs →
      (Fn.whnf f).spec c args h r h' cs
  | .apply_spine, _, _, _, _, _, ev, ih => apply_spine_step c ev ih
  | .peel_beta, _, _, _, _, _, ev, ih => peel_beta_step c ev ih
  | .red_beta, _, _, _, _, _, ev, ih => red_beta_step c ev ih
  | .beta_more, _, _, _, _, _, ev, ih => beta_more_step c ev ih
  | .peel_beta_cert, _, _, _, _, _, ev, ih => peel_beta_cert_step c ev ih
  | .type_sort_never, _, _, _, _, _, ev, ih => type_sort_never_step c ev ih
  | .red_unfold, _, _, _, _, _, ev, ih => red_unfold_step c ev ih
  | .whnf_with_spine, _, _, _, _, _, ev, ih => whnf_with_spine_step c ev ih
  | .whnf_proj_head, _, _, _, _, _, ev, ih => whnf_proj_head_step c ev ih
  | .whnf_spine, _, _, _, _, _, ev, ih => whnf_spine_step c ev ih
  | .try_nat_dispatch_prewhnf, _, _, _, _, _, ev, ih => try_nat_dispatch_prewhnf_step c ev ih
  | .prim_family, _, _, _, _, _, ev, ih => prim_family_step c hc ev ih
  | .try_prim_dispatch, _, _, _, _, _, ev, ih => try_prim_dispatch_step c hc ev ih
  | .whnf_const_head, _, _, _, _, _, ev, ih => whnf_const_head_step c ev ih
  | .lams_never, _, _, _, _, _, ev, ih => lams_never_step c ev ih
  | .projection_definition_info, _, _, _, _, _, ev, ih => projection_definition_info_step c ev ih
  | .nat_lit_to_ctor_or_self, _, _, _, _, _, ev, ih => nat_lit_to_ctor_or_self_step c hc ev ih
  | .slots_never, _, _, _, _, _, ev, ih => slots_never_step c ev ih
  | .certs_all, _, _, _, _, _, ev, ih => certs_all_step c ev ih
  | .apply_n_projs, _, _, _, _, _, ev, ih => apply_n_projs_step c ev ih
  | .whnf, _, _, _, _, _, ev, ih => whnf_step c ev ih
  | .whnf_core, _, _, _, _, _, ev, ih => whnf_core_step c ev ih
  | .whnf_struct_core, _, _, _, _, _, ev, ih => whnf_struct_core_step c ev ih
  | .whnf_struct_core_spine, _, _, _, _, _, ev, ih => whnf_struct_core_spine_step c ev ih
  | .whnf_struct_core_proj, _, _, _, _, _, ev, ih => whnf_struct_core_proj_step c ev ih
  | .whnf_struct_core_const, _, _, _, _, _, ev, ih => whnf_struct_core_const_step c ev ih
  | .whnf_nd, _, _, _, _, _, ev, ih => whnf_nd_step c ev ih
  | .whnf_nd_core, _, _, _, _, _, ev, ih => whnf_nd_core_step c ev ih
  | .whnf_nd_with_spine, _, _, _, _, _, ev, ih => whnf_nd_with_spine_step c ev ih
  | .whnf_nd_proj_head, _, _, _, _, _, ev, ih => whnf_nd_proj_head_step c ev ih
  | .whnf_nd_const_head, _, _, _, _, _, ev, ih => whnf_nd_const_head_step c ev ih
  | .red_iota, _, _, _, _, _, ev, ih => hrest .red_iota (by decide) _ _ _ _ _ ev ih
  | .iota_cmp, _, _, _, _, _, ev, ih => hrest .iota_cmp (by decide) _ _ _ _ _ ev ih
  | .iota_certs, _, _, _, _, _, ev, ih => hrest .iota_certs (by decide) _ _ _ _ _ ev ih
  | .find_rule, _, _, _, _, _, ev, ih => hrest .find_rule (by decide) _ _ _ _ _ ev ih
  | .try_iota, _, _, _, _, _, ev, ih => hrest .try_iota (by decide) _ _ _ _ _ ev ih
  | .whnf_iota_major, _, _, _, _, _, ev, ih => hrest .whnf_iota_major (by decide) _ _ _ _ _ ev ih
  | .pi_peel, _, _, _, _, _, ev, ih => hrest .pi_peel (by decide) _ _ _ _ _ ev ih
  | .pi_residual, _, _, _, _, _, ev, ih => hrest .pi_residual (by decide) _ _ _ _ _ ev ih
  | .k_synth_fab, _, _, _, _, _, ev, ih => hrest .k_synth_fab (by decide) _ _ _ _ _ ev ih
  | .try_k_synth_iota, _, _, _, _, _, ev, ih => hrest .try_k_synth_iota (by decide) _ _ _ _ _ ev ih
  | .eta_iota_fab, _, _, _, _, _, ev, ih => hrest .eta_iota_fab (by decide) _ _ _ _ _ ev ih
  | .try_struct_eta_iota, _, _, _, _, _, ev, ih =>
    hrest .try_struct_eta_iota (by decide) _ _ _ _ _ ev ih
  | .struct_is_rec, _, _, _, _, _, ev, ih => hrest .struct_is_rec (by decide) _ _ _ _ _ ev ih
  | .struct_scan_members, _, _, _, _, _, ev, ih =>
    hrest .struct_scan_members (by decide) _ _ _ _ _ ev ih
  | .struct_block_member_addrs, _, _, _, _, _, ev, ih =>
    hrest .struct_block_member_addrs (by decide) _ _ _ _ _ ev ih
  | .struct_scan_ctors, _, _, _, _, _, ev, ih =>
    hrest .struct_scan_ctors (by decide) _ _ _ _ _ ev ih
  | .se_parent_addr, _, _, _, _, _, ev, ih => hrest .se_parent_addr (by decide) _ _ _ _ _ ev ih
  | .se_peel_tol, _, _, _, _, _, ev, ih => hrest .se_peel_tol (by decide) _ _ _ _ _ ev ih
  | .se_scan_fields, _, _, _, _, _, ev, ih => hrest .se_scan_fields (by decide) _ _ _ _ _ ev ih
  | .se_mentions, _, _, _, _, _, ev, ih => hrest .se_mentions (by decide) _ _ _ _ _ ev ih
  | .se_addr_in, _, _, _, _, _, ev, ih => hrest .se_addr_in (by decide) _ _ _ _ _ ev ih
  | .red_quot, _, _, _, _, _, ev, ih => hrest .red_quot (by decide) _ _ _ _ _ ev ih
  | .quot_certs, _, _, _, _, _, ev, ih => hrest .quot_certs (by decide) _ _ _ _ _ ev ih
  | .try_quot_iota, _, _, _, _, _, ev, ih => hrest .try_quot_iota (by decide) _ _ _ _ _ ev ih
  | .red_rec, _, _, _, _, _, ev, ih => hrest .red_rec (by decide) _ _ _ _ _ ev ih
  | .red_proj, _, _, _, _, _, ev, ih => red_proj_step c hc ev ih
  | .try_reduce_projection_definition, _, _, _, _, _, ev, ih =>
    try_reduce_projection_definition_step c ev ih

end IxVM.Refinement.Core
