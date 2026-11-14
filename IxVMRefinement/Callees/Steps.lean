import IxVMRefinement.Callees.Loads
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Callees.PutConstant
import IxVMRefinement.Callees.Modeled
import IxVMRefinement.Callees.FireCompare

/-! # Callees registry step (`Fn.callees`)

Assembles all 15 functions of `Specs.Callees.Fn` into `callees_step`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

set_option linter.unusedVariables false

/-- **One step per function of the `Callees` family.** -/
theorem callees_step (c : Ctx) (hc : CoreFacts c) :
    ∀ (f : Specs.Callees.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W (Fn.callees f).name args h r h' cs → IH c cs →
        (Fn.callees f).spec c args h r h' cs
  | .get_ci, _, _, _, _, _, ev, _ => get_ci_step c hc ev
  | .get_ci_cprj, _, _, _, _, _, ev, _ => get_ci_cprj_step c hc ev
  | .get_ci_iprj, _, _, _, _, _, ev, _ => get_ci_iprj_step c hc ev
  | .load_verified_constant, _, _, _, _, _, ev, _ => load_verified_constant_step c hc ev
  | .build_recur_addrs, _, _, _, _, _, ev, _ => build_recur_addrs_step c ev
  | .rec_to_parent_addr, _, _, _, _, _, ev, ih => rec_to_parent_addr_step c ev ih
  | .projection_addr_ctor, _, _, _, _, _, ev, _ => projection_addr_ctor_step c ev
  | .put_constant, _, _, _, _, _, ev, _ => put_constant_step c ev
  | .bytes_to_addr, _, _, _, _, _, ev, _ => bytes_to_addr_step c ev
  | .block_is_multi, _, _, _, _, _, ev, ih => block_is_multi_step c ev ih
  | .block_is_modeled, _, _, _, _, _, ev, ih => block_is_modeled_step c ev ih
  | .proj_ctor, _, _, _, _, _, ev, ih => proj_ctor_step c ev ih
  | .defeq_list_ok, _, _, _, _, _, ev, ih => defeq_list_ok_step c ev ih
  | .fire_compare, _, _, _, _, _, ev, ih => fire_compare_step c ev ih
  | .fire_ok, _, _, _, _, _, ev, ih => fire_ok_step c ev ih

end IxVM.Refinement.Core
