import IxVMRefinement.Nat.KlimbsMul
import IxVMRefinement.Nat.Utf8
import IxVMRefinement.Nat.PrimStr
import IxVMRefinement.Nat.PrimNat
import IxVMRefinement.Nat.Levels

/-! # The `Nat` family's steps

`nat_step c hc`: the registry's `Steps` restricted to the `Nat` family (`Core/Specs/Nat.lean`):
every function of `KernelKlimbs`, `KernelNatPrim` and the two `IxVMCompat` division helpers
meets its registered spec, from the induction hypothesis at its derivation's calls. The step
lemmas are in `Nat/{Klimbs,KlimbsMul,Utf8,PrimStr,PrimNat}.lean`; those that read the role table
or the environment take the context's facts (`CoreFacts c`), so the family's share does too. The
`Levels` family's share is `levels_step` (`Nat/Levels.lean`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

/-- **One step per function of the `Nat` family.** -/
theorem nat_step (c : Ctx) (hc : CoreFacts c) :
    ∀ (f : Specs.Nat.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.nat f).name args h r h' cs → IH c cs →
      (Fn.nat f).spec c args h r h' cs
  | .klimbs_succ, _, _, _, _, _, ev, ih => klimbs_succ_step c ev ih
  | .klimbs_add_carry, _, _, _, _, _, ev, ih => klimbs_add_carry_step c ev ih
  | .klimbs_add, _, _, _, _, _, ev, ih => klimbs_add_step c ev ih
  | .klimbs_sub_borrow, _, _, _, _, _, ev, ih => klimbs_sub_borrow_step c ev ih
  | .klimbs_normalize, _, _, _, _, _, ev, ih => klimbs_normalize_step c ev ih
  | .klimbs_sub, _, _, _, _, _, ev, ih => klimbs_sub_step c ev ih
  | .klimbs_le, _, _, _, _, _, ev, ih => klimbs_le_step c ev ih
  | .klimbs_dec, _, _, _, _, _, ev, ih => klimbs_dec_step c ev ih
  | .divmod_256, _, _, _, _, _, ev, ih => divmod_256_step c ev ih
  | .klimbs_mul, _, _, _, _, _, ev, ih => klimbs_mul_step c ev ih
  | .klimbs_mul_outer, _, _, _, _, _, ev, ih => klimbs_mul_outer_step c ev ih
  | .klimbs_mul_single, _, _, _, _, _, ev, ih => klimbs_mul_single_step c ev ih
  | .klimbs_shl_limbs, _, _, _, _, _, ev, ih => klimbs_shl_limbs_step c ev ih
  | .klimbs_is_zero, _, _, _, _, _, ev, ih => klimbs_is_zero_step c ev ih
  | .klimbs_div_mod, _, _, _, _, _, ev, ih => klimbs_div_mod_step c ev ih
  | .klimbs_div, _, _, _, _, _, ev, ih => klimbs_div_step c ev ih
  | .klimbs_mod, _, _, _, _, _, ev, ih => klimbs_mod_step c ev ih
  | .klimbs_gcd, _, _, _, _, _, ev, ih => klimbs_gcd_step c ev ih
  | .klimbs_pow, _, _, _, _, _, ev, ih => klimbs_pow_step c ev ih
  | .klimbs_land, _, _, _, _, _, ev, ih => klimbs_land_step c ev ih
  | .klimbs_lor, _, _, _, _, _, ev, ih => klimbs_lor_step c ev ih
  | .klimbs_xor_op, _, _, _, _, _, ev, ih => klimbs_xor_op_step c ev ih
  | .klimbs_shl, _, _, _, _, _, ev, ih => klimbs_shl_step c ev ih
  | .klimbs_shr, _, _, _, _, _, ev, ih => klimbs_shr_step c ev ih
  | .divide_grow, _, _, _, _, _, ev, ih => divide_grow_step c ev ih
  | .ordinary_div_mod, _, _, _, _, _, ev, ih => ordinary_div_mod_step c ev ih
  | .mk_bool, _, _, _, _, _, ev, ih => mk_bool_step c hc ev ih
  | .mk_nat_lit, _, _, _, _, _, ev, ih => mk_nat_lit_step c ev ih
  | .np_apply_spine, _, _, _, _, _, ev, ih => np_apply_spine_step c ev ih
  | .lvls_empty, _, _, _, _, _, ev, ih => lvls_empty_step c ev ih
  | .split_u32, _, _, _, _, _, ev, ih => split_u32_step c ev ih
  | .klimbs_from_g, _, _, _, _, _, ev, ih => klimbs_from_g_step c ev ih
  | .mk_nat_offset_stuck, _, _, _, _, _, ev, ih => mk_nat_offset_stuck_step c hc ev ih
  | .mk_nat_binop_stuck, _, _, _, _, _, ev, ih => mk_nat_binop_stuck_step c ev ih
  | .build_succ_offset, _, _, _, _, _, ev, ih => build_succ_offset_step c hc ev ih
  | .utf8_cont, _, _, _, _, _, ev, ih => utf8_cont_step c ev ih
  | .utf8_decode_one, _, _, _, _, _, ev, ih => utf8_decode_one_step c ev ih
  | .utf8_validate, _, _, _, _, _, ev, ih => utf8_validate_step c ev ih
  | .build_char_list, _, _, _, _, _, ev, ih => build_char_list_step c ev ih
  | .str_lit_to_ctor, _, _, _, _, _, ev, ih => str_lit_to_ctor_step c hc ev ih
  | .str_lit_delta_step, _, _, _, _, _, ev, ih => str_lit_delta_step_step c ev ih
  | .str_lit_to_ctor_app_or_self, _, _, _, _, _, ev, ih => str_lit_to_ctor_app_or_self_step c ev ih
  | .try_extract_nat, _, _, _, _, _, ev, ih => try_extract_nat_step c hc ev ih
  | .try_extract_nat_app, _, _, _, _, _, ev, ih => try_extract_nat_app_step c hc ev ih
  | .try_nat_binop_addr, _, _, _, _, _, ev, ih => try_nat_binop_addr_step c ev ih
  | .try_match_nat_add, _, _, _, _, _, ev, ih => try_match_nat_add_step c hc ev ih
  | .cleanup_nat_offset_major, _, _, _, _, _, ev, ih => cleanup_nat_offset_major_step c hc ev ih
  | .try_nat_offset_dispatch, _, _, _, _, _, ev, ih => try_nat_offset_dispatch_step c hc ev ih
  | .try_nat_binop_dispatch, _, _, _, _, _, ev, ih => try_nat_binop_dispatch_step c hc ev ih
  | .try_nat_dispatch, _, _, _, _, _, ev, ih => try_nat_dispatch_step c hc ev ih

end IxVM.Refinement.Core
