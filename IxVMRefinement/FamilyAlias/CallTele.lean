import IxVMRefinement.Decl.FamilyTele

/-! # Symmetry and derivation-package wrappers for scoped telescope walks

`Decl/FamilyTele.lean` proves all four scoped telescope walks (`defeq_list_ok_scoped_spec`,
`inst_params_typed_scoped_spec`, `defeq_tele_scoped_spec`, `defeq_lam_tele_scoped_spec`) and
lifts their raw conversion/typing lists to `rulesJ` (`rawDefEqList_rulesJ`,
`rawTypedList_rulesJ`). This module adds `RawDefEqList.symm` for reversing the pairwise
conversion list returned by `defeq_lam_tele_scoped_spec` (and `defeq_list_ok_scoped_spec`). -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core (KExpr)
open Ix.Kernel.Semantics (DefEqListJ)
open Ix.Kernel.Model (rulesJ)

/-- Symmetry of pointwise definitional equality lists (`Rules.DefEq.symm` elementwise). -/
theorem RawDefEqList.symm {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {as bs : List KExpr}, RawDefEqList env d as bs → RawDefEqList env d bs as
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h0, hrest⟩ => ⟨.symm h0, RawDefEqList.symm hrest⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-- Reversed raw conversion list lifted to `rulesJ`. -/
theorem rawDefEqList_symm_rulesJ {env : Ix.Kernel.Env .anon} {d : Nat}
    {as bs : List KExpr} (h : RawDefEqList env d as bs) :
    DefEqListJ rulesJ env d bs as :=
  rawDefEqList_rulesJ (RawDefEqList.symm h)

end IxVM.Refinement.Decl.FamilyAlias
