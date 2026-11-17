import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.RoleVal.LookupSpec

/-! # Membership in the family check's advice set, at a scoped context

`KernelModeled::check_iota_rule` asserts `addr_set_member(t, aset) = 1` for each iota theorem
`t` ("iota theorem is not advice"), and `member_val` the same for each model, against the set
`aset` of advice addresses `check_advice_records` built. `addr_set_member_one_scoped` reads that
answer as membership in the set the tree represents. It is `addr_set_member_one`
(`Decl/ModeledRules.lean`) at a `ScopedCtx`, through the unconditional role-function
specification `RoleVal.roles_fn_spec`, instead of the unrestricted context and `RolesSpec`. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

/-- **`addr_set_member` answering `1`**: the address is in the set the tree represents. -/
theorem addr_set_member_one_scoped {c : ScopedCtx} {advSet : Bytes.Address → Prop}
    {a : Bytes.Address} {t_addr aset : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hwf : c.t.wf = true)
    (ha : Bytes.RepAddressRef addrTy h a t_addr)
    (haset : AddrMapAll addrMapEnum (fun _ k _ => advSet k) h aset)
    (ev : ObsFn W "KernelClaim::addr_set_member" [t_addr, aset] h (.field 1) h' cs) :
    advSet a := by
  obtain ⟨cs4, ev_lkp, _⟩ := Obs.«KernelClaim::addr_set_member».obs ev
  have hfn : Specs.Roles.rbtree_map_lookup_or_default_field c
      [t_addr, aset, .field 0] h (.field 1) h' cs4 :=
    RoleVal.roles_fn_spec c hwf .rbtree_map_lookup_or_default_field _ _ _ _ _ ev_lkp
  rcases hfn t_addr aset (.field 0) rfl a ha (fun _ k _ => advSet k) haset with h01 | hadv
  · injection h01 with hf
    exact absurd hf one_ne_zero
  · exact hadv

end IxVM.Refinement.Decl
