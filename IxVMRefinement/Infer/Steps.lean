import IxVMRefinement.Infer.Leaves
import IxVMRefinement.Infer.Spine
import IxVMRefinement.Infer.Rebase
import IxVMRefinement.Infer.Proj
import IxVMRefinement.Infer.Core

/-! # The `Infer` family's steps

`infer_step c hc hp`: the registry's `Steps` restricted to the `Infer` family
(`Core/Specs/Infer.lean`): every function of `KernelInfer` and `KernelInferOnly` meets its
registered spec, from the induction hypothesis at its derivation's calls. The step lemmas are in
`Infer/{Leaves,Spine,Rebase,Proj,Core}.lean`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

/-- **One step per function of the `Infer` family**. -/
theorem infer_step (c : Ctx) (hc : CoreFacts c) (hp : InferProjFacts c) :
    ∀ (f : Specs.Infer.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.infer f).name args h r h' cs → IH c cs →
      (Fn.infer f).spec c args h r h' cs
  | .types_lookup, _, _, _, _, _, ev, ih => types_lookup_step c ev ih
  | .const_num_lvls, _, _, _, _, _, ev, ih => const_num_lvls_step c ev ih
  | .const_type_of, _, _, _, _, _, ev, ih => const_type_of_step c ev ih
  | .k_infer, _, _, _, _, _, ev, ih => k_infer_step c ev ih
  | .k_infer_rebase, _, _, _, _, _, ev, ih => k_infer_rebase_step c hc ev ih
  | .k_infer_core, _, _, _, _, _, ev, ih => k_infer_core_step c hc ev ih
  | .k_infer_let_start, _, _, _, _, _, ev, ih => k_infer_let_start_step c ev ih
  | .inst_subs, _, _, _, _, _, ev, ih => inst_subs_step c ev ih
  | .k_infer_app_spine_loop, _, _, _, _, _, ev, ih => k_infer_app_spine_loop_step c ev ih
  | .k_infer_lit, _, _, _, _, _, ev, ih => k_infer_lit_step c hc ev ih
  | .peel_params_subst, _, _, _, _, _, ev, ih => peel_params_subst_step c ev ih
  | .is_inductive_prop, _, _, _, _, _, ev, ih => is_inductive_prop_step c ev ih
  | .level_may_be_nonzero, _, _, _, _, _, ev, ih => level_may_be_nonzero_step c ev ih
  | .proj_shape_ok, _, _, _, _, _, ev, ih => proj_shape_ok_step c ev ih
  | .peel_n_alls_whnf, _, _, _, _, _, ev, ih => peel_n_alls_whnf_step c ev ih
  | .peel_field_loop, _, _, _, _, _, ev, ih => peel_field_loop_step c ev ih
  | .k_infer_proj, _, _, _, _, _, ev, ih => k_infer_proj_step c hc hp ev ih
  | .k_ensure_sort, _, _, _, _, _, ev, ih => k_ensure_sort_step c ev ih
  | .k_check, _, _, _, _, _, ev, ih => k_check_step c ev ih
  | .io_types_lookup, _, _, _, _, _, ev, ih => io_types_lookup_step c ev ih
  | .io_const_num_lvls, _, _, _, _, _, ev, ih => io_const_num_lvls_step c ev ih
  | .io_const_type_of, _, _, _, _, _, ev, ih => io_const_type_of_step c ev ih
  | .k_infer_only, _, _, _, _, _, ev, ih => k_infer_only_step c ev ih
  | .k_infer_only_core, _, _, _, _, _, ev, ih => k_infer_only_core_step c hc hp ev ih
  | .io_app_cod, _, _, _, _, _, ev, ih => io_app_cod_step c ev ih
  | .forall_datum_ok, _, _, _, _, _, ev, ih => forall_datum_ok_step c ev ih
  | .lam_datum_ok, _, _, _, _, _, ev, ih => lam_datum_ok_step c ev ih
  | .ensure_sort_only, _, _, _, _, _, ev, ih => ensure_sort_only_step c ev ih
  | .io_peel_params_subst, _, _, _, _, _, ev, ih => io_peel_params_subst_step c ev ih

end IxVM.Refinement.Core
