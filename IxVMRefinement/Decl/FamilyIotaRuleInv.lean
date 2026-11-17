import IxVMRefinement.Decl.ModeledRules

/-! # Inversion of `KernelModeled::check_iota_rule`

`KernelModeled::check_iota_rule` has no generated path lemma (`IxVMRefinement/Obs.lean` skips it
as too costly), so its observation is inverted here by hand over `ObsFn`/`ObsExpr`, step by step
through the source body (`IxVM/IxVM/Source/KernelModeled.lean`).

The body types the stored rule on its renaming to the model: `rhs_m = rename(rhs, src, dst)` is
inferred (`k_infer(rc, rhs_m, nil)`), and reused for the rule's λ-telescope walk and for the right
side's application; `ty_m = rename(ty_r, src, dst)` is the statement's prefix and the rule's side's
telescope; the constructor's comparands are typed against `rename(cty_l, src, dst)` at the renamed
pins `pins_ren`.

* `CheckIotaRuleInvR`: every intermediate value, heap, call slice and callee observation of the
  body, in body order, with the call-list containments (`SubCalls`) the consumers need.
* `check_iota_rule_invR`: an observation of `check_iota_rule` yields that record. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Direct inversion of `KernelModeled::check_iota_rule` -/

private theorem invR_var_find {locals : Environment F Nat} {name : String} {v expected : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hlkp : locals.find? (·.1 == name) = some (name, expected))
    (ev : ObsExpr W [] locals (.var name) h v h' cs) :
    expected = v ∧ h = h' ∧ cs = [] := by
  obtain ⟨l, hh, hc⟩ := ev.var_inv
  rw [hlkp] at l
  injection l with l; injection l with _ hv
  exact ⟨hv, hh.symm, hc⟩

private theorem invR_lit {locals : Environment F Nat} {x : F} {v : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsExpr W [] locals (.literal x) h v h' cs) :
    v = .field x ∧ h = h' ∧ cs = [] :=
  let ⟨hv, hh, hc⟩ := ev.literal_inv; ⟨hv, hh.symm, hc⟩

private theorem invR_nil {locals : Environment F Nat} {vs : List (SourceValue F)}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [] h vs h' cs) :
    vs = [] ∧ h = h' ∧ cs = [] :=
  let ⟨hv, hh, hc⟩ := ev.nil_inv; ⟨hv, hh.symm, hc⟩

private theorem invR_store_nil_kexpr {locals : Environment F Nat} {v : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsExpr W [] locals
      (.store (.construct "Lists::Node" (some [.ptr (.named "KernelTypes::KExprNode" [])]) "Nil" []))
      h v h' cs) :
    v = .ptr (.enum kexprListEnum) h.length ∧
      h' = h ++ [.construct kexprListEnum "Nil" []] ∧ cs = [] := by
  obtain ⟨inp, mid, d, rfl, rfl⟩ := ev.store_inv
  obtain ⟨vals, a, hres⟩ := d.construct_inv
  rw [kexprList_inst] at hres
  subst hres
  obtain ⟨rfl, rfl, rfl⟩ := a.nil_inv
  exact ⟨by simp [Value.type], rfl, rfl⟩

/-- Structured record of all intermediate heaps, values, call slices, and sub-derivations extracted
from `ObsFn W "KernelModeled::check_iota_rule"`, in the order of the body. The renamed terms are
named: `rhs_m` (the rule, renamed before it is inferred), `ty_m` (the recursor type, renamed
before the statement's prefix comparison), `v_cty_ren` (the constructor type renamed for
`inst_params`) and `v_cty_ren2` (renamed again for `inst_params_typed`). -/
structure CheckIotaRuleInvR
    (rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset : SourceValue F)
    (h : Heap F) (calls : List (Call F)) where
  mi : SourceValue F
  d : SourceValue F
  op_mi : evalBinOp .add rp ni = .ok mi
  op_d : evalBinOp .add rp cnf = .ok d
  h_plen : Heap F
  cs_plen : List (Call F)
  call_plen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [pins], h⟩ : Call F) ∈ calls
  ev_plen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [pins] h cnp h_plen cs_plen
  -- stored rule front-end
  v_sc : SourceValue F
  h_sc : Heap F
  cs_sc : List (Call F)
  ev_sc : ObsFn W "KernelCheck::validate_expr_well_scoped" [rhs, .field 0, nl] h_plen v_sc h_sc cs_sc
  sub_sc : SubCalls calls cs_sc
  r_peel_e : SourceValue F
  r_peel_acc : SourceValue F
  h_peel : Heap F
  cs_peel : List (Call F)
  ev_peel : ObsFn W "KernelCheck::peel_n_lams_collect"
    [rhs, d, .field 0, .ptr (.enum kexprListEnum) h_sc.length]
    (h_sc ++ [.construct kexprListEnum "Nil" []])
    (.tuple [r_peel_e, d, r_peel_acc]) h_peel cs_peel
  rhs_m : SourceValue F
  h_rhs_m : Heap F
  cs_rhs_m : List (Call F)
  ev_rhs_m : ObsFn W "KernelModeled::rename" [rhs, src, dst] h_peel rhs_m h_rhs_m cs_rhs_m
  sub_rhs_m : SubCalls calls cs_rhs_m
  v_rhs_ty : SourceValue F
  h_rhs_inf : Heap F
  cs_rhs_inf : List (Call F)
  ev_rhs_inf : ObsFn W "KernelInfer::k_infer"
    [rc, rhs_m, .ptr (.enum kexprListEnum) h_rhs_m.length]
    (h_rhs_m ++ [.construct kexprListEnum "Nil" []]) v_rhs_ty h_rhs_inf cs_rhs_inf
  sub_rhs_inf : SubCalls calls cs_rhs_inf
  -- advice theorem lookup and opening
  h_aset : Heap F
  cs_aset : List (Call F)
  ev_aset : ObsFn W "KernelClaim::addr_set_member" [t_addr, aset] h_rhs_inf (.field 1) h_aset cs_aset
  sub_aset : SubCalls calls cs_aset
  p_tci : SourceValue F
  h_tci : Heap F
  cs_tci : List (Call F)
  ev_tci : ObsFn W "Ingress::get_ci" [t_addr] h_aset p_tci h_tci cs_tci
  sub_tci : SubCalls calls cs_tci
  tty : SourceValue F
  w_tval : SourceValue F
  ld_tci : loadValue h_tci p_tci = .ok (.construct kciEnum "Thm" [nl, tty, w_tval])
  tbody : SourceValue F
  ctx : SourceValue F
  h_open : Heap F
  cs_open : List (Call F)
  ev_open : ObsFn W "KernelModeled::peel_collect"
    [tty, d, .ptr (.enum kexprListEnum) h_tci.length]
    (h_tci ++ [.construct kexprListEnum "Nil" []]) (.tuple [tbody, ctx]) h_open cs_open
  -- equation spine
  eqh : SourceValue F
  targs : SourceValue F
  h_tsp : Heap F
  cs_tsp : List (Call F)
  ev_tsp : ObsFn W "KernelTypes::collect_spine" [tbody] h_open (.tuple [eqh, targs]) h_tsp cs_tsp
  eqa : SourceValue F
  eqls : SourceValue F
  ld_eqh : loadValue h_tsp eqh = .ok (.construct kexprEnum "Const" [eqa, eqls])
  v_req : SourceValue F
  h_req : Heap F
  cs_req : List (Call F)
  v_raddr : SourceValue F
  h_raddr : Heap F
  cs_raddr : List (Call F)
  h_eqa : Heap F
  cs_eqa : List (Call F)
  ev_req : ObsFn W "KernelRoleSpec::role_eq" [] h_tsp v_req h_req cs_req
  ev_raddr : ObsFn W "KernelRoles::role_addr" [rc, v_req] h_req v_raddr h_raddr cs_raddr
  sub_raddr : SubCalls calls cs_raddr
  ev_eqa : ObsFn W "Bytes::address_eq" [eqa, v_raddr] h_raddr (.field 1) h_eqa cs_eqa
  ell : SourceValue F
  eqrest : SourceValue F
  ld_eqls1 : loadValue h_eqa eqls = .ok (.construct klevelListEnum "Cons" [ell, eqrest])
  ld_eqls2 : loadValue h_eqa eqrest = .ok (.construct klevelListEnum "Nil" [])
  h_tlen : Heap F
  cs_tlen : List (Call F)
  call_tlen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [targs], h_eqa⟩ : Call F) ∈ calls
  ev_tlen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [targs] h_eqa (.field 3) h_tlen cs_tlen
  alpha : SourceValue F
  lhs : SourceValue F
  rhs_s : SourceValue F
  h_a0 : Heap F
  cs_a0 : List (Call F)
  h_a1 : Heap F
  cs_a1 : List (Call F)
  h_a2 : Heap F
  cs_a2 : List (Call F)
  ev_a0 : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [targs, .field 0] h_tlen alpha h_a0 cs_a0
  ev_a1 : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [targs, .field 1] h_a0 lhs h_a1 cs_a1
  ev_a2 : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [targs, .field 2] h_a1 rhs_s h_a2 cs_a2
  -- lhs spine, head, prefix, and major
  lh : SourceValue F
  largs : SourceValue F
  h_lsp : Heap F
  cs_lsp : List (Call F)
  ev_lsp : ObsFn W "KernelTypes::collect_spine" [lhs] h_a2 (.tuple [lh, largs]) h_lsp cs_lsp
  v_plvls : SourceValue F
  h_plvls : Heap F
  cs_plvls : List (Call F)
  ev_plvls : ObsFn W "KernelCheck::build_param_lvls_range" [.field 0, nl, .field 0] h_lsp v_plvls h_plvls cs_plvls
  h_lheq : Heap F
  cs_lheq : List (Call F)
  ev_lheq : ObsFn W "KernelCheck::kexpr_struct_eq"
    [lh, .ptr (.enum kexprEnum) h_plvls.length]
    (h_plvls ++ [.construct kexprEnum "Const" [rm, v_plvls]]) (.field 1) h_lheq cs_lheq
  mi1 : SourceValue F
  op_mi1 : evalBinOp .add mi (.field 1) = .ok mi1
  h_llen : Heap F
  cs_llen : List (Call F)
  call_llen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [largs], h_lheq⟩ : Call F) ∈ calls
  ev_llen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [largs] h_lheq mi1 h_llen cs_llen
  v_ltake : SourceValue F
  h_ltake : Heap F
  cs_ltake : List (Call F)
  v_bvd1 : SourceValue F
  h_bvd1 : Heap F
  cs_bvd1 : List (Call F)
  h_pref : Heap F
  cs_pref : List (Call F)
  ev_ltake : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [largs, rp] h_llen v_ltake h_ltake cs_ltake
  ev_bvd1 : ObsFn W "KernelModeled::bvars_desc" [d, rp] h_ltake v_bvd1 h_bvd1 cs_bvd1
  ev_pref : ObsFn W "KernelCheck::spec_params_ptr_eq" [v_ltake, v_bvd1] h_bvd1 (.field 1) h_pref cs_pref
  major : SourceValue F
  h_maj : Heap F
  cs_maj : List (Call F)
  ev_maj : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [largs, mi] h_pref major h_maj cs_maj
  cren : SourceValue F
  h_cren : Heap F
  cs_cren : List (Call F)
  ev_cren : ObsFn W "KernelModeled::rename_addr" [cprj, src, dst] h_maj cren h_cren cs_cren
  pins_ren : SourceValue F
  h_pren : Heap F
  cs_pren : List (Call F)
  ev_pren : ObsFn W "KernelModeled::rename_list" [pins, src, dst] h_cren pins_ren h_pren cs_pren
  pins_d : SourceValue F
  h_pd : Heap F
  cs_pd : List (Call F)
  ev_pd : ObsFn W "KernelModeled::lift_list" [pins_ren, cnf] h_pren pins_d h_pd cs_pd
  sub_pd : SubCalls calls cs_pd
  v_bvd2 : SourceValue F
  h_bvd2 : Heap F
  cs_bvd2 : List (Call F)
  v_cat : SourceValue F
  h_cat : Heap F
  cs_cat : List (Call F)
  expected : SourceValue F
  h_exp : Heap F
  cs_exp : List (Call F)
  h_majeq : Heap F
  cs_majeq : List (Call F)
  ev_bvd2 : ObsFn W "KernelModeled::bvars_desc" [cnf, cnf]
    (h_pd ++ [.construct kexprEnum "Const" [cren, ilvls]]) v_bvd2 h_bvd2 cs_bvd2
  ev_cat : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [pins_d, v_bvd2] h_bvd2 v_cat h_cat cs_cat
  ev_exp : ObsFn W "KernelWhnf::apply_spine"
    [.ptr (.enum kexprEnum) h_pd.length, v_cat] h_cat expected h_exp cs_exp
  ev_majeq : ObsFn W "KernelCheck::kexpr_struct_eq" [major, expected] h_exp (.field 1) h_majeq cs_majeq
  -- constructor telescope and indices
  cty_l : SourceValue F
  h_ctyl : Heap F
  cs_ctyl : List (Call F)
  ev_ctyl : ObsFn W "KernelLevels::expr_inst_levels" [cty, ilvls] h_majeq cty_l h_ctyl cs_ctyl
  sub_ctyl : SubCalls calls cs_ctyl
  cnp_cnf : SourceValue F
  op_cnp_cnf : evalBinOp .add cnp cnf = .ok cnp_cnf
  v_peel0 : SourceValue F
  h_peel0 : Heap F
  cs_peel0 : List (Call F)
  chead0 : SourceValue F
  cargs0 : SourceValue F
  h_csp0 : Heap F
  cs_csp0 : List (Call F)
  ev_peel0 : ObsFn W "KernelCheck::peel_n_foralls" [cty_l, cnp_cnf] h_ctyl v_peel0 h_peel0 cs_peel0
  ev_csp0 : ObsFn W "KernelTypes::collect_spine" [v_peel0] h_peel0 (.tuple [chead0, cargs0]) h_csp0 cs_csp0
  sub_csp0 : SubCalls calls cs_csp0
  w_ch0a : SourceValue F
  w_ch0b : SourceValue F
  ld_chead0 : loadValue h_csp0 chead0 = .ok (.construct kexprEnum "Const" [w_ch0a, w_ch0b])
  v_cty_ren : SourceValue F
  h_cty_ren : Heap F
  cs_cty_ren : List (Call F)
  crest : SourceValue F
  h_crest : Heap F
  cs_crest : List (Call F)
  ev_cty_ren : ObsFn W "KernelModeled::rename" [cty_l, src, dst] h_csp0 v_cty_ren h_cty_ren cs_cty_ren
  sub_cty_ren : SubCalls calls cs_cty_ren
  ev_crest : ObsFn W "KernelModeled::inst_params" [v_cty_ren, pins_ren] h_cty_ren crest h_crest cs_crest
  sub_crest : SubCalls calls cs_crest
  cres : SourceValue F
  w_cctx : SourceValue F
  h_cres : Heap F
  cs_cres : List (Call F)
  ev_cres : ObsFn W "KernelModeled::peel_collect"
    [crest, cnf, .ptr (.enum kexprListEnum) h_crest.length]
    (h_crest ++ [.construct kexprListEnum "Nil" []]) (.tuple [cres, w_cctx]) h_cres cs_cres
  chead : SourceValue F
  cargs : SourceValue F
  h_csp : Heap F
  cs_csp : List (Call F)
  ev_csp : ObsFn W "KernelTypes::collect_spine" [cres] h_cres (.tuple [chead, cargs]) h_csp cs_csp
  sub_csp : SubCalls calls cs_csp
  w_cha : SourceValue F
  w_chb : SourceValue F
  ld_chead : loadValue h_csp chead = .ok (.construct kexprEnum "Const" [w_cha, w_chb])
  cnp_ni : SourceValue F
  op_cnp_ni : evalBinOp .add cnp ni = .ok cnp_ni
  h_clen : Heap F
  cs_clen : List (Call F)
  call_clen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [cargs], h_csp⟩ : Call F) ∈ calls
  ev_clen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [cargs] h_csp cnp_ni h_clen cs_clen
  v_ldrop : SourceValue F
  h_ldrop : Heap F
  cs_ldrop : List (Call F)
  v_idxl : SourceValue F
  h_idxl : Heap F
  cs_idxl : List (Call F)
  v_idxr : SourceValue F
  h_idxr : Heap F
  cs_idxr : List (Call F)
  h_deidx : Heap F
  cs_deidx : List (Call F)
  ev_ldrop : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [largs, rp] h_clen v_ldrop h_ldrop cs_ldrop
  ev_idxl : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [v_ldrop, ni] h_ldrop v_idxl h_idxl cs_idxl
  ev_idxr : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [cargs, cnp] h_idxl v_idxr h_idxr cs_idxr
  ev_deidx : ObsFn W "KernelModeled::defeq_list_ok" [rc, v_idxl, v_idxr, ctx] h_idxr (.field 1) h_deidx cs_deidx
  sub_deidx : SubCalls calls cs_deidx
  -- statement domain telescopes: the renamed recursor type `ty_m`
  ty_m : SourceValue F
  h_ty_m : Heap F
  cs_ty_m : List (Call F)
  ev_ty_m : ObsFn W "KernelModeled::rename" [ty_r, src, dst] h_deidx ty_m h_ty_m cs_ty_m
  sub_ty_m : SubCalls calls cs_ty_m
  v_dt1 : SourceValue F
  h_dt1 : Heap F
  cs_dt1 : List (Call F)
  ev_dt1 : ObsFn W "KernelModeled::defeq_tele"
    [rc, tty, ty_m, rp, .ptr (.enum kexprListEnum) h_ty_m.length]
    (h_ty_m ++ [.construct kexprListEnum "Nil" []]) v_dt1 h_dt1 cs_dt1
  sub_dt1 : SubCalls calls cs_dt1
  v_tty_rp : SourceValue F
  h_tty_rp : Heap F
  cs_tty_rp : List (Call F)
  v_ctx_rp : SourceValue F
  h_ctx_rp : Heap F
  cs_ctx_rp : List (Call F)
  v_dt2 : SourceValue F
  h_dt2 : Heap F
  cs_dt2 : List (Call F)
  ev_tty_rp : ObsFn W "KernelCheck::peel_n_foralls" [tty, rp] h_dt1 v_tty_rp h_tty_rp cs_tty_rp
  ev_ctx_rp : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [ctx, cnf] h_tty_rp v_ctx_rp h_ctx_rp cs_ctx_rp
  ev_dt2 : ObsFn W "KernelModeled::defeq_tele" [rc, v_tty_rp, crest, cnf, v_ctx_rp] h_ctx_rp v_dt2 h_dt2 cs_dt2
  sub_dt2 : SubCalls calls cs_dt2
  -- the rule's side, renamed: parameter typing and λ-telescope walks
  w_pbody : SourceValue F
  ctx_p : SourceValue F
  h_ctxp : Heap F
  cs_ctxp : List (Call F)
  ev_ctxp : ObsFn W "KernelModeled::peel_collect"
    [ty_m, rp, .ptr (.enum kexprListEnum) h_dt2.length]
    (h_dt2 ++ [.construct kexprListEnum "Nil" []]) (.tuple [w_pbody, ctx_p]) h_ctxp cs_ctxp
  v_cty_ren2 : SourceValue F
  h_cty_ren2 : Heap F
  cs_cty_ren2 : List (Call F)
  ev_cty_ren2 : ObsFn W "KernelModeled::rename" [cty_l, src, dst] h_ctxp v_cty_ren2 h_cty_ren2 cs_cty_ren2
  sub_cty_ren2 : SubCalls calls cs_cty_ren2
  crest_p : SourceValue F
  h_crestp : Heap F
  cs_crestp : List (Call F)
  ev_crestp : ObsFn W "KernelModeled::inst_params_typed" [rc, v_cty_ren2, pins_ren, ctx_p]
    h_cty_ren2 crest_p h_crestp cs_crestp
  sub_crestp : SubCalls calls cs_crestp
  rhs_rp : SourceValue F
  lctx : SourceValue F
  h_lt1 : Heap F
  cs_lt1 : List (Call F)
  ev_lt1 : ObsFn W "KernelModeled::defeq_lam_tele"
    [rc, rhs_m, ty_m, rp, .ptr (.enum kexprListEnum) h_crestp.length]
    (h_crestp ++ [.construct kexprListEnum "Nil" []]) (.tuple [rhs_rp, lctx]) h_lt1 cs_lt1
  sub_lt1 : SubCalls calls cs_lt1
  w_lt2a : SourceValue F
  w_lt2b : SourceValue F
  h_lt2 : Heap F
  cs_lt2 : List (Call F)
  ev_lt2 : ObsFn W "KernelModeled::defeq_lam_tele" [rc, rhs_rp, crest_p, cnf, lctx] h_lt1 (.tuple [w_lt2a, w_lt2b]) h_lt2 cs_lt2
  sub_lt2 : SubCalls calls cs_lt2
  -- rhs application (of the renamed rule `rhs_m`) and defeq
  v_bvd3 : SourceValue F
  h_bvd3 : Heap F
  cs_bvd3 : List (Call F)
  rhs_app : SourceValue F
  h_rhsapp : Heap F
  cs_rhsapp : List (Call F)
  h_derhs : Heap F
  cs_derhs : List (Call F)
  ev_bvd3 : ObsFn W "KernelModeled::bvars_desc" [d, d] h_lt2 v_bvd3 h_bvd3 cs_bvd3
  ev_rhsapp : ObsFn W "KernelWhnf::apply_spine" [rhs_m, v_bvd3] h_bvd3 rhs_app h_rhsapp cs_rhsapp
  ev_derhs : ObsFn W "KernelDefEq::k_is_def_eq" [rc, rhs_s, rhs_app, ctx] h_rhsapp (.field 1) h_derhs cs_derhs
  sub_derhs : SubCalls calls cs_derhs
  -- lhs, rhs, and alpha typing
  tl : SourceValue F
  h_tl : Heap F
  cs_tl : List (Call F)
  h_detl : Heap F
  cs_detl : List (Call F)
  tr : SourceValue F
  h_tr : Heap F
  cs_tr : List (Call F)
  h_detr : Heap F
  cs_detr : List (Call F)
  ta : SourceValue F
  h_ta : Heap F
  cs_ta : List (Call F)
  h_deta : Heap F
  cs_deta : List (Call F)
  ev_tl : ObsFn W "KernelInfer::k_infer" [rc, lhs, ctx] h_derhs tl h_tl cs_tl
  sub_tl : SubCalls calls cs_tl
  ev_detl : ObsFn W "KernelDefEq::k_is_def_eq" [rc, tl, alpha, ctx] h_tl (.field 1) h_detl cs_detl
  sub_detl : SubCalls calls cs_detl
  ev_tr : ObsFn W "KernelInfer::k_infer" [rc, rhs_s, ctx] h_detl tr h_tr cs_tr
  sub_tr : SubCalls calls cs_tr
  ev_detr : ObsFn W "KernelDefEq::k_is_def_eq" [rc, tr, alpha, ctx] h_tr (.field 1) h_detr cs_detr
  sub_detr : SubCalls calls cs_detr
  ev_ta : ObsFn W "KernelInfer::k_infer" [rc, alpha, ctx] h_detr ta h_ta cs_ta
  sub_ta : SubCalls calls cs_ta
  ev_deta : ObsFn W "KernelDefEq::k_is_def_eq"
    [rc, ta, .ptr (.enum kexprEnum) h_ta.length, ctx]
    (h_ta ++ [.construct kexprEnum "Srt" [ell]]) (.field 1) h_deta cs_deta
  sub_deta : SubCalls calls cs_deta

private theorem invR_args1 {locals : Environment F Nat} {e₁ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁] h vs h' cs) :
    ∃ v₁, vs = [v₁] ∧ ObsExpr W [] locals e₁ h v₁ h' cs := by
  obtain ⟨v₁, _, m₁, c₁, c₂, rfl, d₁, an, rfl⟩ := ev.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := an.nil_inv
  exact ⟨v₁, rfl, by simpa using d₁⟩

private theorem invR_args2 {locals : Environment F Nat} {e₁ e₂ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂] h vs h' cs) :
    ∃ v₁ v₂ m₁ c₁ c₂, vs = [v₁, v₂] ∧ cs = c₁ ++ c₂ ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ h' c₂ := by
  obtain ⟨v₁, _, m₁, c₁, c₂, rfl, d₁, a₂, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, rfl, d₂⟩ := invR_args1 a₂
  exact ⟨v₁, v₂, m₁, c₁, c₂, rfl, rfl, d₁, d₂⟩

private theorem invR_args3 {locals : Environment F Nat} {e₁ e₂ e₃ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂, e₃] h vs h' cs) :
    ∃ v₁ v₂ v₃ m₁ m₂ c₁ c₂ c₃, vs = [v₁, v₂, v₃] ∧ cs = c₁ ++ (c₂ ++ c₃) ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ m₂ c₂ ∧
      ObsExpr W [] locals e₃ m₂ v₃ h' c₃ := by
  obtain ⟨v₁, _, m₁, c₁, cr, rfl, d₁, ar, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, v₃, m₂, c₂, c₃, rfl, rfl, d₂, d₃⟩ := invR_args2 ar
  exact ⟨v₁, v₂, v₃, m₁, m₂, c₁, c₂, c₃, rfl, rfl, d₁, d₂, d₃⟩

private theorem invR_args4 {locals : Environment F Nat} {e₁ e₂ e₃ e₄ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂, e₃, e₄] h vs h' cs) :
    ∃ v₁ v₂ v₃ v₄ m₁ m₂ m₃ c₁ c₂ c₃ c₄, vs = [v₁, v₂, v₃, v₄] ∧
      cs = c₁ ++ (c₂ ++ (c₃ ++ c₄)) ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ m₂ c₂ ∧
      ObsExpr W [] locals e₃ m₂ v₃ m₃ c₃ ∧ ObsExpr W [] locals e₄ m₃ v₄ h' c₄ := by
  obtain ⟨v₁, _, m₁, c₁, cr, rfl, d₁, ar, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, v₃, v₄, m₂, m₃, c₂, c₃, c₄, rfl, rfl, d₂, d₃, d₄⟩ := invR_args3 ar
  exact ⟨v₁, v₂, v₃, v₄, m₁, m₂, m₃, c₁, c₂, c₃, c₄, rfl, rfl, d₁, d₂, d₃, d₄⟩

private theorem invR_args5 {locals : Environment F Nat} {e₁ e₂ e₃ e₄ e₅ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂, e₃, e₄, e₅] h vs h' cs) :
    ∃ v₁ v₂ v₃ v₄ v₅ m₁ m₂ m₃ m₄ c₁ c₂ c₃ c₄ c₅, vs = [v₁, v₂, v₃, v₄, v₅] ∧
      cs = c₁ ++ (c₂ ++ (c₃ ++ (c₄ ++ c₅))) ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ m₂ c₂ ∧
      ObsExpr W [] locals e₃ m₂ v₃ m₃ c₃ ∧ ObsExpr W [] locals e₄ m₃ v₄ m₄ c₄ ∧
      ObsExpr W [] locals e₅ m₄ v₅ h' c₅ := by
  obtain ⟨v₁, _, m₁, c₁, cr, rfl, d₁, ar, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, v₃, v₄, v₅, m₂, m₃, m₄, c₂, c₃, c₄, c₅, rfl, rfl, d₂, d₃, d₄, d₅⟩ := invR_args4 ar
  exact ⟨v₁, v₂, v₃, v₄, v₅, m₁, m₂, m₃, m₄, c₁, c₂, c₃, c₄, c₅, rfl, rfl, d₁, d₂, d₃, d₄, d₅⟩

private theorem invR_match_kexpr_const_unit {locals : Environment F Nat} {scr : String}
    {ptr : SourceValue F} {rest : Aiur.Generic.Expr F} {h h' : Heap F}
    {r : SourceValue F} {cs : List (Call F)} {calls : List (Call F)}
    (hlkp : locals.find? (·.1 == scr) = some (scr, ptr))
    (sc : SubCalls calls cs)
    (ev : ObsExpr W [] locals
      (.letValue .wildcard
        (.matchValue (.load (.var scr))
          [(.construct (.named "KernelTypes::KExprNode" []) "Const" [.wildcard, .wildcard], .tuple [])])
        rest) h r h' cs) :
    ∃ w₁ w₂ cs_rest,
      loadValue h ptr = .ok (.construct kexprEnum "Const" [w₁, w₂]) ∧
      SubCalls calls cs_rest ∧
      ObsExpr W [] locals rest h r h' cs_rest := by
  obtain ⟨_, m₁, _, c₁, cs_rest, dm, mt_w, drest, hc⟩ := ev.letValue_inv
  rw [hc] at sc
  obtain rfl := matchPattern_wildcard_inv mt_w
  obtain ⟨_, m_ld, _, _, _, _, dld, sel, darm, _⟩ := dm.matchValue_inv
  obtain ⟨_, dv, ld⟩ := dld.load_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find hlkp dv
  rcases selectArm_cons_inv sel with ⟨mt_c, rfl⟩ | ⟨nm_c, sel_nil⟩
  · obtain ⟨vs, hv, -, ml₁⟩ := matchPattern_construct_inv mt_c
    rw [kexpr_ctor] at hv; subst hv
    obtain ⟨w₁, _, _, _, rfl, mtw₁, ml₂, rfl⟩ := matchListWith_cons_inv ml₁
    obtain rfl := matchPattern_wildcard_inv mtw₁
    obtain ⟨w₂, _, _, _, rfl, mtw₂, ml₃, rfl⟩ := matchListWith_cons_inv ml₂
    obtain rfl := matchPattern_wildcard_inv mtw₂
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml₃
    obtain ⟨_, a_tup, rfl⟩ := darm.tuple_inv
    obtain ⟨rfl, rfl, _⟩ := invR_nil a_tup
    exact ⟨w₁, w₂, cs_rest, ld, sc.append_right, drest⟩
  · exact (selectArm_nil_inv sel_nil).elim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- Direct expression-level inversion of `KernelModeled::check_iota_rule`'s body: the stored
rule renamed before it is inferred (`rhs_m`), the renamed recursor type (`ty_m`) for the
statement's prefix and the rule's side, the constructor type renamed for `inst_params_typed` at
the renamed pins. -/
theorem check_iota_rule_invR
    {rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::check_iota_rule"
      [rc, rm, nl, ty_r, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins, t_addr, src, dst, aset]
      h r h' calls) :
    Nonempty (CheckIotaRuleInvR rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset h calls) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelModeled.check_iota_rule.lookup
    (by simp [IxVM.KernelModeled.check_iota_rule, ControlLower.hasControl]) ev
  simp only [IxVM.KernelModeled.check_iota_rule] at d0
  have hcalls₀ : ∃ calls₀, calls₀ = calls ∧ SubCalls calls₀ calls :=
    ⟨calls, rfl, SubCalls.refl calls⟩
  obtain ⟨calls₀, hcalls₀_eq, sc0⟩ := hcalls₀
  -- 1. `let mi = rp + ni`
  obtain ⟨mi, _, _, _, _, d1, mt1, rest1, hc1⟩ := d0.letValue_inv; clear d0
  rw [hc1] at sc0; have sc1 := sc0.append_right; clear sc0 hc1
  obtain ⟨_, _, _, _, _, dl1, dr1, op_mi, _⟩ := d1.binary_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) dl1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) dr1
  obtain rfl := matchPattern_bind_inv mt1
  -- 2. `let d = rp + cnf`
  obtain ⟨d, _, _, _, _, d2, mt2, rest2, hc2⟩ := rest1.letValue_inv; clear rest1
  rw [hc2] at sc1; have sc2 := sc1.append_right; clear sc1 hc2
  obtain ⟨_, _, _, _, _, dl2, dr2, op_d, _⟩ := d2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) dl2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) dr2
  obtain rfl := matchPattern_bind_inv mt2
  -- 3. `assert_eq!(Lists::length(pins), cnp)`
  obtain ⟨_, m3, _, c3a, _, d3, mt3, rest3, hc3⟩ := rest2.letValue_inv; clear rest2
  rw [hc3] at sc2; have sc3_l := sc2.append_left; have sc3 := sc2.append_right; clear sc2 hc3
  obtain ⟨_, a3, ap3⟩ := d3.builtin_inv
  obtain ⟨v3_l, v3_r, h_plen, c3_l, c3_r, rfl, hc3_args, d3_l, d3_r⟩ := invR_args2 a3
  obtain ⟨_, _, _, cs_plen, a3_la, ev_plen, hc_plen⟩ := d3_l.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_plen hc_plen
  obtain ⟨_, rfl, d3_lv⟩ := invR_args1 a3_la
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d3_lv
  obtain ⟨rfl, hm3, rfl⟩ := invR_var_find (by rfl) d3_r; subst m3
  obtain ⟨heq3, rfl⟩ := Builtin.assertEq_inv ap3; subst v3_l
  obtain rfl := matchPattern_wildcard_inv mt3
  rw [hc3_args, hc_plen] at sc3_l
  have call_plen := sc3_l.append_left.append_right.cons_head
  clear sc3_l hc3_args hc_plen
  -- 4. `KernelCheck::validate_expr_well_scoped(rhs, 0, nl)`
  obtain ⟨v_sc, h_sc, _, c4a, _, d4, mt4, rest4, hc4⟩ := rest3.letValue_inv; clear rest3
  rw [hc4] at sc3; have sc4_l := sc3.append_left; have sc4 := sc3.append_right; clear sc3 hc4
  obtain ⟨_, m4_3, _, cs_sc, a4, ev_sc, hc_sc⟩ := d4.call_inv
  rw [instanceName_plain_some] at ev_sc hc_sc
  obtain ⟨_, _, _, m4_1, m4_2, _, _, _, rfl, hc4_args, d4_1, d4_2, d4_3⟩ := invR_args3 a4
  obtain ⟨rfl, hm4_1, rfl⟩ := invR_var_find (by rfl) d4_1; subst m4_1
  obtain ⟨rfl, hm4_2, rfl⟩ := invR_lit d4_2; subst m4_2
  obtain ⟨rfl, hm4_3, rfl⟩ := invR_var_find (by rfl) d4_3; subst m4_3
  obtain rfl := matchPattern_wildcard_inv mt4
  rw [hc_sc, hc4_args] at sc4_l
  have sub_sc := sc4_l.append_right.cons_tail
  clear sc4_l hc_sc hc4_args
  -- 5. `let (_, peeled, _) = KernelCheck::peel_n_lams_collect(rhs, d, 0, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_peel, _, _, _, d5, mt5, rest5, hc5⟩ := rest4.letValue_inv; clear rest4
  rw [hc5] at sc4; have sc5 := sc4.append_right; clear sc4 hc5
  obtain ⟨_, _, _, cs_peel, a5, ev_peel, _⟩ := d5.call_inv
  rw [instanceName_plain_some] at ev_peel
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d5_1, d5_2, d5_3, d5_4⟩ := invR_args4 a5
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d5_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d5_2
  obtain ⟨rfl, rfl, _⟩ := invR_lit d5_3
  obtain ⟨rfl, rfl, _⟩ := invR_store_nil_kexpr d5_4
  obtain ⟨_, hv5, -, ml5a⟩ := matchPattern_tuple_inv mt5; subst hv5
  obtain ⟨r_peel_e, _, _, _, rfl, mt5_1, ml5b, rfl⟩ := matchListWith_cons_inv ml5a
  obtain rfl := matchPattern_wildcard_inv mt5_1
  obtain ⟨peeled_v, _, _, _, rfl, mt5_2, ml5c, rfl⟩ := matchListWith_cons_inv ml5b
  obtain rfl := matchPattern_bind_inv mt5_2
  obtain ⟨r_peel_acc, _, _, _, rfl, mt5_3, ml5d, rfl⟩ := matchListWith_cons_inv ml5c
  obtain rfl := matchPattern_wildcard_inv mt5_3
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml5d
  -- 6. `assert_eq!(peeled, d)`
  obtain ⟨_, _, _, _, _, d6, mt6, rest6, hc6⟩ := rest5.letValue_inv; clear rest5
  rw [hc6] at sc5; have sc6 := sc5.append_right; clear sc5 hc6
  obtain ⟨_, a6, ap6⟩ := d6.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d6_1, d6_2⟩ := invR_args2 a6
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d6_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d6_2
  obtain ⟨heq6, rfl⟩ := Builtin.assertEq_inv ap6; subst peeled_v
  obtain rfl := matchPattern_wildcard_inv mt6
  -- 7a. `let rhs_m = rename(rhs, src, dst)`
  obtain ⟨rhs_m, h_rhs_m, _, c7ra, _, d7r, mt7r, rest7r, hc7r⟩ := rest6.letValue_inv; clear rest6
  rw [hc7r] at sc6; have sc7r_l := sc6.append_left; have sc7r := sc6.append_right; clear sc6 hc7r
  obtain ⟨_, _, _, cs_rhs_m, a7r, ev_rhs_m, hc_rhs_m⟩ := d7r.call_inv
  rw [instanceName_plain_some] at ev_rhs_m hc_rhs_m
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d7r_1, d7r_2, d7r_3⟩ := invR_args3 a7r
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d7r_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d7r_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d7r_3
  obtain rfl := matchPattern_bind_inv mt7r
  rw [hc_rhs_m] at sc7r_l
  have sub_rhs_m := sc7r_l.append_right.cons_tail
  clear sc7r_l hc_rhs_m
  -- 7b. `KernelInfer::k_infer(rc, rhs_m, (&(Lists::Node::Nil)))`
  obtain ⟨v_rhs_ty, h_rhs_inf, _, c7a, _, d7, mt7, rest7, hc7⟩ := rest7r.letValue_inv; clear rest7r
  rw [hc7] at sc7r; have sc7_l := sc7r.append_left; have sc7 := sc7r.append_right; clear sc7r hc7
  obtain ⟨_, _, _, cs_rhs_inf, a7, ev_rhs_inf, hc_rhs_inf⟩ := d7.call_inv
  rw [instanceName_plain_some] at ev_rhs_inf hc_rhs_inf
  obtain ⟨_, _, _, _, _, _, _, _, rfl, hc7_args, d7_1, d7_2, d7_3⟩ := invR_args3 a7
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d7_1
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d7_2
  obtain ⟨rfl, rfl, rfl⟩ := invR_store_nil_kexpr d7_3
  obtain rfl := matchPattern_wildcard_inv mt7
  rw [hc_rhs_inf, hc7_args] at sc7_l
  have sub_rhs_inf := sc7_l.append_right.cons_tail
  clear sc7_l hc_rhs_inf hc7_args
  -- 8. `assert_eq!(KernelClaim::addr_set_member(t, aset), 1)`
  obtain ⟨_, h_aset, _, c8a, _, d8, mt8, rest8, hc8⟩ := rest7.letValue_inv; clear rest7
  rw [hc8] at sc7; have sc8_l := sc7.append_left; have sc8 := sc7.append_right; clear sc7 hc8
  obtain ⟨_, a8, ap8⟩ := d8.builtin_inv
  obtain ⟨v_aset_m, _, _, c8_l, c8_r, rfl, hc8_args, d8_1, d8_2⟩ := invR_args2 a8
  obtain ⟨_, _, _, cs_aset, a8_c, ev_aset, hc_aset⟩ := d8_1.call_inv
  rw [instanceName_plain_some] at ev_aset hc_aset
  obtain ⟨_, _, _, _, _, rfl, hc8_cargs, d8_c1, d8_c2⟩ := invR_args2 a8_c
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d8_c1
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d8_c2
  obtain ⟨rfl, rfl, rfl⟩ := d8_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap8
  obtain rfl := matchPattern_wildcard_inv mt8
  rw [hc8_args, hc_aset, hc8_cargs] at sc8_l
  have sub_aset := sc8_l.append_left.append_right.cons_tail
  clear sc8_l hc8_args hc_aset hc8_cargs
  -- 9. `match (*(Ingress::get_ci(t))) { KernelTypes::KConstantInfo::Thm(tnl, tty, _) => { ... } }`
  obtain ⟨_, h_tci, _, _, c9a, c9b, d9_scr, sel9, rest9, hc9⟩ := rest8.matchValue_inv; clear rest8
  rw [hc9] at sc8; have sc9_l := sc8.append_left; have sc9 := sc8.append_right; clear sc8 hc9
  obtain ⟨p_tci, d9_call, ld_tci⟩ := d9_scr.load_inv
  obtain ⟨_, _, _, cs_tci, a9, ev_tci, hc_tci⟩ := d9_call.call_inv
  rw [instanceName_plain_some] at ev_tci hc_tci
  obtain ⟨_, rfl, d9_t⟩ := invR_args1 a9
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d9_t
  rw [hc_tci] at sc9_l
  have sub_tci := sc9_l.append_right.cons_tail
  clear sc9_l hc_tci
  rcases selectArm_cons_inv sel9 with ⟨mt9, rfl⟩ | ⟨_, sel9_nil⟩
  swap; · exact (selectArm_nil_inv sel9_nil).elim
  obtain ⟨_, hv9, -, ml9a⟩ := matchPattern_construct_inv mt9
  rw [Obs.Names.n11677430323439928978] at hv9; subst hv9
  obtain ⟨tnl, _, _, _, rfl, mt9_1, ml9b, rfl⟩ := matchListWith_cons_inv ml9a
  obtain rfl := matchPattern_bind_inv mt9_1
  obtain ⟨tty, _, _, _, rfl, mt9_2, ml9c, rfl⟩ := matchListWith_cons_inv ml9b
  obtain rfl := matchPattern_bind_inv mt9_2
  obtain ⟨w_tval, _, _, _, rfl, mt9_3, ml9d, rfl⟩ := matchListWith_cons_inv ml9c
  obtain rfl := matchPattern_wildcard_inv mt9_3
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml9d
  -- 10. `assert_eq!(tnl, nl)`
  obtain ⟨_, _, _, _, _, d10, mt10, rest10, hc10⟩ := rest9.letValue_inv; clear rest9
  rw [hc10] at sc9; have sc10 := sc9.append_right; clear sc9 hc10
  obtain ⟨_, a10, ap10⟩ := d10.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d10_1, d10_2⟩ := invR_args2 a10
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d10_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d10_2
  obtain ⟨heq10, rfl⟩ := Builtin.assertEq_inv ap10; subst tnl
  obtain rfl := matchPattern_wildcard_inv mt10
  -- 11. `let (tbody, ctx) = peel_collect(tty, d, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_open, _, _, _, d11, mt11, rest11, hc11⟩ := rest10.letValue_inv; clear rest10
  rw [hc11] at sc10; have sc11 := sc10.append_right; clear sc10 hc11
  obtain ⟨_, _, _, cs_open, a11, ev_open, _⟩ := d11.call_inv
  rw [instanceName_plain_some] at ev_open
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d11_1, d11_2, d11_3⟩ := invR_args3 a11
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d11_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d11_2
  obtain ⟨rfl, rfl, _⟩ := invR_store_nil_kexpr d11_3
  obtain ⟨_, hv11, -, ml11a⟩ := matchPattern_tuple_inv mt11; subst hv11
  obtain ⟨tbody, _, _, _, rfl, mt11_1, ml11b, rfl⟩ := matchListWith_cons_inv ml11a
  obtain rfl := matchPattern_bind_inv mt11_1
  obtain ⟨ctx, _, _, _, rfl, mt11_2, ml11c, rfl⟩ := matchListWith_cons_inv ml11b
  obtain rfl := matchPattern_bind_inv mt11_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml11c
  -- 12. `let (eqh, targs) = KernelTypes::collect_spine(tbody)`
  obtain ⟨_, h_tsp, _, _, _, d12, mt12, rest12, hc12⟩ := rest11.letValue_inv; clear rest11
  rw [hc12] at sc11; have sc12 := sc11.append_right; clear sc11 hc12
  obtain ⟨_, _, _, cs_tsp, a12, ev_tsp, _⟩ := d12.call_inv
  rw [instanceName_plain_some] at ev_tsp
  obtain ⟨_, rfl, d12_1⟩ := invR_args1 a12
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d12_1
  obtain ⟨_, hv12, -, ml12a⟩ := matchPattern_tuple_inv mt12; subst hv12
  obtain ⟨eqh, _, _, _, rfl, mt12_1, ml12b, rfl⟩ := matchListWith_cons_inv ml12a
  obtain rfl := matchPattern_bind_inv mt12_1
  obtain ⟨targs, _, _, _, rfl, mt12_2, ml12c, rfl⟩ := matchListWith_cons_inv ml12b
  obtain rfl := matchPattern_bind_inv mt12_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml12c
  -- 13. `match (*(eqh)) { KernelTypes::KExprNode::Const(eqa, eqls) => { ... } }`
  obtain ⟨_, _, _, _, _, _, d13_scr, sel13, rest13, hc13⟩ := rest12.matchValue_inv; clear rest12
  rw [hc13] at sc12; have sc13 := sc12.append_right; clear sc12 hc13
  obtain ⟨_, d13_v, ld_eqh⟩ := d13_scr.load_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d13_v
  rcases selectArm_cons_inv sel13 with ⟨mt13, rfl⟩ | ⟨_, sel13_nil⟩
  swap; · exact (selectArm_nil_inv sel13_nil).elim
  obtain ⟨_, hv13, -, ml13a⟩ := matchPattern_construct_inv mt13
  rw [kexpr_ctor] at hv13; subst hv13
  obtain ⟨eqa, _, _, _, rfl, mt13_1, ml13b, rfl⟩ := matchListWith_cons_inv ml13a
  obtain rfl := matchPattern_bind_inv mt13_1
  obtain ⟨eqls, _, _, _, rfl, mt13_2, ml13c, rfl⟩ := matchListWith_cons_inv ml13b
  obtain rfl := matchPattern_bind_inv mt13_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml13c
  -- 14. `assert_eq!(Bytes::address_eq(eqa, KernelRoles::role_addr(rc, KernelRoleSpec::role_eq())), 1)`
  obtain ⟨_, h_eqa, _, c14a, _, d14, mt14, rest14, hc14⟩ := rest13.letValue_inv; clear rest13
  rw [hc14] at sc13; have sc14_l := sc13.append_left; have sc14 := sc13.append_right; clear sc13 hc14
  obtain ⟨_, a14, ap14⟩ := d14.builtin_inv
  obtain ⟨_, _, _, c14_l, _, rfl, hc14_args, d14_1, d14_2⟩ := invR_args2 a14
  obtain ⟨_, h_raddr, c14_eqa, cs_eqa, a14_eq, ev_eqa, hc_eqa⟩ := d14_1.call_inv
  rw [instanceName_plain_some] at ev_eqa hc_eqa
  obtain ⟨_, v_raddr, _, c14_ea1, c14_ea2, rfl, hc14_ea, d14_eqa, d14_ra⟩ := invR_args2 a14_eq
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d14_eqa
  obtain ⟨_, h_req, c14_raa, cs_raddr, a14_ra, ev_raddr, hc_raddr⟩ := d14_ra.call_inv
  rw [instanceName_plain_some] at ev_raddr hc_raddr
  obtain ⟨_, v_req, _, _, c14_req, rfl, hc14_raa, d14_rc, d14_req⟩ := invR_args2 a14_ra
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d14_rc
  obtain ⟨_, _, _, cs_req, a14_req, ev_req, _⟩ := d14_req.call_inv
  rw [instanceName_plain_some] at ev_req
  obtain ⟨rfl, rfl, rfl⟩ := invR_nil a14_req
  obtain ⟨rfl, rfl, rfl⟩ := d14_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap14
  obtain rfl := matchPattern_wildcard_inv mt14
  rw [hc14_args, hc_eqa, hc14_ea, hc_raddr] at sc14_l
  have sub_raddr :=
    sc14_l.append_left.append_left.append_right.append_right.cons_tail
  clear sc14_l hc14_args hc_eqa hc14_ea hc_raddr hc14_raa
  -- 15. `let Lists::Node::Cons(ell, eqrest) = (*(eqls))`
  obtain ⟨_, _, _, _, _, d15, mt15, rest15, hc15⟩ := rest14.letValue_inv; clear rest14
  rw [hc15] at sc14; have sc15 := sc14.append_right; clear sc14 hc15
  obtain ⟨_, d15_v, ld_eqls1⟩ := d15.load_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d15_v
  obtain ⟨_, hv15, -, ml15a⟩ := matchPattern_construct_inv mt15
  rw [klevelList_ctor] at hv15; subst hv15
  obtain ⟨ell, _, _, _, rfl, mt15_1, ml15b, rfl⟩ := matchListWith_cons_inv ml15a
  obtain rfl := matchPattern_bind_inv mt15_1
  obtain ⟨eqrest, _, _, _, rfl, mt15_2, ml15c, rfl⟩ := matchListWith_cons_inv ml15b
  obtain rfl := matchPattern_bind_inv mt15_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml15c
  -- 16. `let Lists::Node::Nil = (*(eqrest))`
  obtain ⟨_, _, _, _, _, d16, mt16, rest16, hc16⟩ := rest15.letValue_inv; clear rest15
  rw [hc16] at sc15; have sc16 := sc15.append_right; clear sc15 hc16
  obtain ⟨_, d16_v, ld_eqls2⟩ := d16.load_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d16_v
  obtain ⟨_, hv16, -, ml16⟩ := matchPattern_construct_inv mt16
  rw [klevelList_ctor] at hv16; subst hv16
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml16
  -- 17. `assert_eq!(Lists::length(targs), 3)`
  obtain ⟨_, h_tlen, _, c17a, _, d17, mt17, rest17, hc17⟩ := rest16.letValue_inv; clear rest16
  rw [hc17] at sc16; have sc17_l := sc16.append_left; have sc17 := sc16.append_right; clear sc16 hc17
  obtain ⟨_, a17, ap17⟩ := d17.builtin_inv
  obtain ⟨_, _, _, c17_l, _, rfl, hc17_args, d17_1, d17_2⟩ := invR_args2 a17
  obtain ⟨_, _, _, cs_tlen, a17_c, ev_tlen, hc_tlen⟩ := d17_1.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_tlen hc_tlen
  obtain ⟨_, rfl, d17_v⟩ := invR_args1 a17_c
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d17_v
  obtain ⟨rfl, rfl, rfl⟩ := d17_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap17
  obtain rfl := matchPattern_wildcard_inv mt17
  rw [hc17_args, hc_tlen] at sc17_l
  have call_tlen := sc17_l.append_left.append_right.cons_head
  clear sc17_l hc17_args hc_tlen
  -- 18. `let alpha = Lists::lookup(targs, 0)`
  obtain ⟨alpha, h_a0, _, _, _, d18, mt18, rest18, hc18⟩ := rest17.letValue_inv; clear rest17
  rw [hc18] at sc17; have sc18 := sc17.append_right; clear sc17 hc18
  obtain ⟨_, _, _, cs_a0, a18, ev_a0, _⟩ := d18.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_a0
  obtain ⟨_, _, _, _, _, rfl, _, d18_1, d18_2⟩ := invR_args2 a18
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d18_1
  obtain ⟨rfl, rfl, _⟩ := invR_lit d18_2
  obtain rfl := matchPattern_bind_inv mt18
  -- 19. `let lhs = Lists::lookup(targs, 1)`
  obtain ⟨lhs, h_a1, _, _, _, d19, mt19, rest19, hc19⟩ := rest18.letValue_inv; clear rest18
  rw [hc19] at sc18; have sc19 := sc18.append_right; clear sc18 hc19
  obtain ⟨_, _, _, cs_a1, a19, ev_a1, _⟩ := d19.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_a1
  obtain ⟨_, _, _, _, _, rfl, _, d19_1, d19_2⟩ := invR_args2 a19
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d19_1
  obtain ⟨rfl, rfl, _⟩ := invR_lit d19_2
  obtain rfl := matchPattern_bind_inv mt19
  -- 20. `let rhs_s = Lists::lookup(targs, 2)`
  obtain ⟨rhs_s, h_a2, _, _, _, d20, mt20, rest20, hc20⟩ := rest19.letValue_inv; clear rest19
  rw [hc20] at sc19; have sc20 := sc19.append_right; clear sc19 hc20
  obtain ⟨_, _, _, cs_a2, a20, ev_a2, _⟩ := d20.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_a2
  obtain ⟨_, _, _, _, _, rfl, _, d20_1, d20_2⟩ := invR_args2 a20
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d20_1
  obtain ⟨rfl, rfl, _⟩ := invR_lit d20_2
  obtain rfl := matchPattern_bind_inv mt20
  -- 21. `let (lh, largs) = KernelTypes::collect_spine(lhs)`
  obtain ⟨_, h_lsp, _, _, _, d21, mt21, rest21, hc21⟩ := rest20.letValue_inv; clear rest20
  rw [hc21] at sc20; have sc21 := sc20.append_right; clear sc20 hc21
  obtain ⟨_, _, _, cs_lsp, a21, ev_lsp, _⟩ := d21.call_inv
  rw [instanceName_plain_some] at ev_lsp
  obtain ⟨_, rfl, d21_1⟩ := invR_args1 a21
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d21_1
  obtain ⟨_, hv21, -, ml21a⟩ := matchPattern_tuple_inv mt21; subst hv21
  obtain ⟨lh, _, _, _, rfl, mt21_1, ml21b, rfl⟩ := matchListWith_cons_inv ml21a
  obtain rfl := matchPattern_bind_inv mt21_1
  obtain ⟨largs, _, _, _, rfl, mt21_2, ml21c, rfl⟩ := matchListWith_cons_inv ml21b
  obtain rfl := matchPattern_bind_inv mt21_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml21c
  -- 22. `let rhead = (&(KernelTypes::KExprNode::Const(rm, KernelCheck::build_param_lvls_range(0, nl, 0))))`
  obtain ⟨_, _, _, _, _, d22, mt22, rest22, hc22⟩ := rest21.letValue_inv; clear rest21
  rw [hc22] at sc21; have sc22 := sc21.append_right; clear sc21 hc22
  obtain ⟨inp22, h_plvls, d22_c, rfl, rfl⟩ := d22.store_inv
  obtain ⟨_, a22_c, hres22⟩ := d22_c.construct_inv
  rw [instanceName_plain_some] at hres22; subst hres22
  obtain ⟨_, v_plvls, _, _, _, rfl, _, d22_rm, d22_pl⟩ := invR_args2 a22_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d22_rm
  obtain ⟨_, _, _, cs_plvls, a22_pl, ev_plvls, _⟩ := d22_pl.call_inv
  rw [instanceName_plain_some] at ev_plvls
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d22_p1, d22_p2, d22_p3⟩ := invR_args3 a22_pl
  obtain ⟨rfl, rfl, _⟩ := invR_lit d22_p1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d22_p2
  obtain ⟨rfl, rfl, _⟩ := invR_lit d22_p3
  obtain rfl := matchPattern_bind_inv mt22
  -- 23. `assert_eq!(KernelCheck::kexpr_struct_eq(lh, rhead), 1)`
  obtain ⟨_, h_lheq, _, _, _, d23, mt23, rest23, hc23⟩ := rest22.letValue_inv; clear rest22
  rw [hc23] at sc22; have sc23 := sc22.append_right; clear sc22 hc23
  obtain ⟨_, a23, ap23⟩ := d23.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d23_1, d23_2⟩ := invR_args2 a23
  obtain ⟨_, _, _, cs_lheq, a23_c, ev_lheq, _⟩ := d23_1.call_inv
  rw [instanceName_plain_some] at ev_lheq
  obtain ⟨_, _, _, _, _, rfl, _, d23_c1, d23_c2⟩ := invR_args2 a23_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d23_c1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d23_c2
  obtain ⟨rfl, rfl, _⟩ := d23_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap23
  simp only [Value.type] at ev_lheq
  obtain rfl := matchPattern_wildcard_inv mt23
  -- 24. `assert_eq!(Lists::length(largs), mi + 1)`
  obtain ⟨_, h_llen, _, c24a, _, d24, mt24, rest24, hc24⟩ := rest23.letValue_inv; clear rest23
  rw [hc24] at sc23; have sc24_l := sc23.append_left; have sc24 := sc23.append_right; clear sc23 hc24
  obtain ⟨_, a24, ap24⟩ := d24.builtin_inv
  obtain ⟨v_llen, mi1, _, c24_l, _, rfl, hc24_args, d24_1, d24_2⟩ := invR_args2 a24
  obtain ⟨_, _, _, cs_llen, a24_c, ev_llen, hc_llen⟩ := d24_1.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_llen hc_llen
  obtain ⟨_, rfl, d24_v⟩ := invR_args1 a24_c
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d24_v
  obtain ⟨_, _, _, _, _, d24_b1, d24_b2, op_mi1, _⟩ := d24_2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d24_b1
  obtain ⟨rfl, rfl, _⟩ := d24_b2.literal_inv
  obtain ⟨heq24, rfl⟩ := Builtin.assertEq_inv ap24; subst v_llen
  obtain rfl := matchPattern_wildcard_inv mt24
  rw [hc24_args, hc_llen] at sc24_l
  have call_llen := sc24_l.append_left.append_right.cons_head
  clear sc24_l hc24_args hc_llen
  -- 25. `assert_eq!(KernelCheck::spec_params_ptr_eq(Lists::take(largs, rp), bvars_desc(d, rp)), 1)`
  obtain ⟨_, h_pref, _, _, _, d25, mt25, rest25, hc25⟩ := rest24.letValue_inv; clear rest24
  rw [hc25] at sc24; have sc25 := sc24.append_right; clear sc24 hc25
  obtain ⟨_, a25, ap25⟩ := d25.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d25_1, d25_2⟩ := invR_args2 a25
  obtain ⟨_, h_bvd1, _, cs_pref, a25_c, ev_pref, _⟩ := d25_1.call_inv
  rw [instanceName_plain_some] at ev_pref
  obtain ⟨v_ltake, v_bvd1, h_ltake, _, _, rfl, _, d25_tk, d25_bv⟩ := invR_args2 a25_c
  obtain ⟨_, _, _, cs_ltake, a25_tk, ev_ltake, _⟩ := d25_tk.call_inv
  rw [Obs.Names.n3863982424408310192] at ev_ltake
  obtain ⟨_, _, _, _, _, rfl, _, d25_tk1, d25_tk2⟩ := invR_args2 a25_tk
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d25_tk1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d25_tk2
  obtain ⟨_, _, _, cs_bvd1, a25_bv, ev_bvd1, _⟩ := d25_bv.call_inv
  rw [instanceName_plain_some] at ev_bvd1
  obtain ⟨_, _, _, _, _, rfl, _, d25_bv1, d25_bv2⟩ := invR_args2 a25_bv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d25_bv1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d25_bv2
  obtain ⟨rfl, rfl, _⟩ := d25_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap25
  obtain rfl := matchPattern_wildcard_inv mt25
  -- 26. `let major = Lists::lookup(largs, mi)`
  obtain ⟨major, h_maj, _, _, _, d26, mt26, rest26, hc26⟩ := rest25.letValue_inv; clear rest25
  rw [hc26] at sc25; have sc26 := sc25.append_right; clear sc25 hc26
  obtain ⟨_, _, _, cs_maj, a26, ev_maj, _⟩ := d26.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_maj
  obtain ⟨_, _, _, _, _, rfl, _, d26_1, d26_2⟩ := invR_args2 a26
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d26_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d26_2
  obtain rfl := matchPattern_bind_inv mt26
  -- 27. `let cren = rename_addr(cprj, src, dst)`
  obtain ⟨cren, h_cren, _, _, _, d27, mt27, rest27, hc27⟩ := rest26.letValue_inv; clear rest26
  rw [hc27] at sc26; have sc27 := sc26.append_right; clear sc26 hc27
  obtain ⟨_, _, _, cs_cren, a27, ev_cren, _⟩ := d27.call_inv
  rw [instanceName_plain_some] at ev_cren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d27_1, d27_2, d27_3⟩ := invR_args3 a27
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d27_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d27_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d27_3
  obtain rfl := matchPattern_bind_inv mt27
  -- 28. `let pins_ren = rename_list(pins, src, dst)`
  obtain ⟨pins_ren, h_pren, _, _, _, d28, mt28, rest28, hc28⟩ := rest27.letValue_inv; clear rest27
  rw [hc28] at sc27; have sc28 := sc27.append_right; clear sc27 hc28
  obtain ⟨_, _, _, cs_pren, a28, ev_pren, _⟩ := d28.call_inv
  rw [instanceName_plain_some] at ev_pren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d28_1, d28_2, d28_3⟩ := invR_args3 a28
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d28_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d28_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d28_3
  obtain rfl := matchPattern_bind_inv mt28
  -- 29. `let pins_d = lift_list(pins_ren, cnf)`
  obtain ⟨pins_d, h_pd, _, c29a, _, d29, mt29, rest29, hc29⟩ := rest28.letValue_inv; clear rest28
  rw [hc29] at sc28; have sc29_l := sc28.append_left; have sc29 := sc28.append_right; clear sc28 hc29
  obtain ⟨_, _, _, cs_pd, a29, ev_pd, hc_pd⟩ := d29.call_inv
  rw [instanceName_plain_some] at ev_pd hc_pd
  obtain ⟨_, _, _, _, _, rfl, hc29_args, d29_1, d29_2⟩ := invR_args2 a29
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d29_1
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d29_2
  obtain rfl := matchPattern_bind_inv mt29
  rw [hc_pd, hc29_args] at sc29_l
  have sub_pd := sc29_l.append_right.cons_tail
  clear sc29_l hc_pd hc29_args
  -- 30. `let expected = KernelWhnf::apply_spine((&(Const(cren, ilvls))), Lists::concat(pins_d, bvars_desc(cnf, cnf)))`
  obtain ⟨expected, h_exp, _, _, _, d30, mt30, rest30, hc30⟩ := rest29.letValue_inv; clear rest29
  rw [hc30] at sc29; have sc30 := sc29.append_right; clear sc29 hc30
  obtain ⟨_, h_cat, _, cs_exp, a30, ev_exp, _⟩ := d30.call_inv
  rw [instanceName_plain_some] at ev_exp
  obtain ⟨_, v_cat, _, _, _, rfl, _, d30_1, d30_2⟩ := invR_args2 a30
  obtain ⟨_, _, d30_c, rfl, rfl⟩ := d30_1.store_inv
  obtain ⟨_, a30_c, hres30⟩ := d30_c.construct_inv
  rw [instanceName_plain_some] at hres30; subst hres30
  obtain ⟨_, _, _, _, _, rfl, _, d30_c1, d30_c2⟩ := invR_args2 a30_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d30_c1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d30_c2
  simp only [Value.type] at ev_exp
  obtain ⟨_, h_bvd2, _, cs_cat, a30_cat, ev_cat, _⟩ := d30_2.call_inv
  rw [Obs.Names.n7100276142009841923] at ev_cat
  obtain ⟨_, v_bvd2, _, _, _, rfl, _, d30_pd, d30_bv⟩ := invR_args2 a30_cat
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d30_pd
  obtain ⟨_, _, _, cs_bvd2, a30_bv, ev_bvd2, _⟩ := d30_bv.call_inv
  rw [instanceName_plain_some] at ev_bvd2
  obtain ⟨_, _, _, _, _, rfl, _, d30_bv1, d30_bv2⟩ := invR_args2 a30_bv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d30_bv1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d30_bv2
  obtain rfl := matchPattern_bind_inv mt30
  -- 31. `assert_eq!(KernelCheck::kexpr_struct_eq(major, expected), 1)`
  obtain ⟨_, h_majeq, _, _, _, d31, mt31, rest31, hc31⟩ := rest30.letValue_inv; clear rest30
  rw [hc31] at sc30; have sc31 := sc30.append_right; clear sc30 hc31
  obtain ⟨_, a31, ap31⟩ := d31.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d31_1, d31_2⟩ := invR_args2 a31
  obtain ⟨_, _, _, cs_majeq, a31_c, ev_majeq, _⟩ := d31_1.call_inv
  rw [instanceName_plain_some] at ev_majeq
  obtain ⟨_, _, _, _, _, rfl, _, d31_c1, d31_c2⟩ := invR_args2 a31_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d31_c1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d31_c2
  obtain ⟨rfl, rfl, _⟩ := d31_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap31
  obtain rfl := matchPattern_wildcard_inv mt31
  -- 32. `let cty_l = KernelLevels::expr_inst_levels(cty, ilvls)`
  obtain ⟨cty_l, h_ctyl, _, c32a, _, d32, mt32, rest32, hc32⟩ := rest31.letValue_inv; clear rest31
  rw [hc32] at sc31; have sc32_l := sc31.append_left; have sc32 := sc31.append_right; clear sc31 hc32
  obtain ⟨_, _, _, cs_ctyl, a32, ev_ctyl, hc_ctyl⟩ := d32.call_inv
  rw [instanceName_plain_some] at ev_ctyl hc_ctyl
  obtain ⟨_, _, _, _, _, rfl, hc32_args, d32_1, d32_2⟩ := invR_args2 a32
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d32_1
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d32_2
  obtain rfl := matchPattern_bind_inv mt32
  rw [hc_ctyl, hc32_args] at sc32_l
  have sub_ctyl := sc32_l.append_right.cons_tail
  clear sc32_l hc_ctyl hc32_args
  -- 33. `let (chead0, _) = KernelTypes::collect_spine(KernelCheck::peel_n_foralls(cty_l, cnp + cnf))`
  obtain ⟨_, h_csp0, _, c33a, _, d33, mt33, rest33, hc33⟩ := rest32.letValue_inv; clear rest32
  rw [hc33] at sc32; have sc33_l := sc32.append_left; have sc33 := sc32.append_right; clear sc32 hc33
  obtain ⟨_, h_peel0, c33_spargs, cs_csp0, a33, ev_csp0, hc_csp0⟩ := d33.call_inv
  rw [instanceName_plain_some] at ev_csp0 hc_csp0
  obtain ⟨v_peel0, rfl, d33_p⟩ := invR_args1 a33
  obtain ⟨_, _, _, cs_peel0, a33_p, ev_peel0, _⟩ := d33_p.call_inv
  rw [instanceName_plain_some] at ev_peel0
  obtain ⟨_, cnp_cnf, _, _, _, rfl, _, d33_p1, d33_p2⟩ := invR_args2 a33_p
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d33_p1
  obtain ⟨_, _, _, _, _, d33_b1, d33_b2, op_cnp_cnf, _⟩ := d33_p2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d33_b1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d33_b2
  obtain ⟨_, hv33, -, ml33a⟩ := matchPattern_tuple_inv mt33; subst hv33
  obtain ⟨chead0, _, _, _, rfl, mt33_1, ml33b, rfl⟩ := matchListWith_cons_inv ml33a
  obtain rfl := matchPattern_bind_inv mt33_1
  obtain ⟨cargs0, _, _, _, rfl, mt33_2, ml33c, rfl⟩ := matchListWith_cons_inv ml33b
  obtain rfl := matchPattern_wildcard_inv mt33_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml33c
  rw [hc_csp0] at sc33_l
  have sub_csp0 := sc33_l.append_right.cons_tail
  clear sc33_l hc_csp0
  -- 34. `match (*(chead0)) { Const(_, _) => { () } };`
  obtain ⟨w_ch0a, w_ch0b, _, ld_chead0, sc34, rest34⟩ :=
    invR_match_kexpr_const_unit (by rfl) sc33 rest33; clear sc33 rest33
  -- 35. `let crest = inst_params(rename(cty_l, src, dst), pins_ren)`
  obtain ⟨crest, h_crest, _, c35a, _, d35, mt35, rest35, hc35⟩ := rest34.letValue_inv; clear rest34
  rw [hc35] at sc34; have sc35_l := sc34.append_left; have sc35 := sc34.append_right; clear sc34 hc35
  obtain ⟨_, _, c35_args, cs_crest, a35, ev_crest, hc_crest⟩ := d35.call_inv
  rw [instanceName_plain_some] at ev_crest hc_crest
  obtain ⟨v_cty_ren, _, h_cty_ren, c35_1, _, rfl, hc35_args, d35_1, d35_2⟩ := invR_args2 a35
  obtain ⟨_, _, _, cs_cty_ren, a35_r, ev_cty_ren, hc_cty_ren⟩ := d35_1.call_inv
  rw [instanceName_plain_some] at ev_cty_ren hc_cty_ren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d35_r1, d35_r2, d35_r3⟩ := invR_args3 a35_r
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d35_r1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d35_r2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d35_r3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d35_2
  obtain rfl := matchPattern_bind_inv mt35
  rw [hc_crest, hc35_args, hc_cty_ren] at sc35_l
  have sub_cty_ren := sc35_l.append_left.append_left.append_right.cons_tail
  have sub_crest := sc35_l.append_right.cons_tail
  clear sc35_l hc_crest hc35_args hc_cty_ren
  -- 36. `let (cres, _) = peel_collect(crest, cnf, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_cres, _, _, _, d36, mt36, rest36, hc36⟩ := rest35.letValue_inv; clear rest35
  rw [hc36] at sc35; have sc36 := sc35.append_right; clear sc35 hc36
  obtain ⟨_, _, _, cs_cres, a36, ev_cres, _⟩ := d36.call_inv
  rw [instanceName_plain_some] at ev_cres
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d36_1, d36_2, d36_3⟩ := invR_args3 a36
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d36_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d36_2
  obtain ⟨rfl, rfl, _⟩ := invR_store_nil_kexpr d36_3
  obtain ⟨_, hv36, -, ml36a⟩ := matchPattern_tuple_inv mt36; subst hv36
  obtain ⟨cres, _, _, _, rfl, mt36_1, ml36b, rfl⟩ := matchListWith_cons_inv ml36a
  obtain rfl := matchPattern_bind_inv mt36_1
  obtain ⟨w_cctx, _, _, _, rfl, mt36_2, ml36c, rfl⟩ := matchListWith_cons_inv ml36b
  obtain rfl := matchPattern_wildcard_inv mt36_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml36c
  -- 37. `let (chead, cargs) = KernelTypes::collect_spine(cres)`
  obtain ⟨_, h_csp, _, c37a, _, d37, mt37, rest37, hc37⟩ := rest36.letValue_inv; clear rest36
  rw [hc37] at sc36; have sc37_l := sc36.append_left; have sc37 := sc36.append_right; clear sc36 hc37
  obtain ⟨_, _, _, cs_csp, a37, ev_csp, hc_csp⟩ := d37.call_inv
  rw [instanceName_plain_some] at ev_csp hc_csp
  obtain ⟨_, rfl, d37_1⟩ := invR_args1 a37
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d37_1
  obtain ⟨_, hv37, -, ml37a⟩ := matchPattern_tuple_inv mt37; subst hv37
  obtain ⟨chead, _, _, _, rfl, mt37_1, ml37b, rfl⟩ := matchListWith_cons_inv ml37a
  obtain rfl := matchPattern_bind_inv mt37_1
  obtain ⟨cargs, _, _, _, rfl, mt37_2, ml37c, rfl⟩ := matchListWith_cons_inv ml37b
  obtain rfl := matchPattern_bind_inv mt37_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml37c
  rw [hc_csp] at sc37_l
  have sub_csp := sc37_l.append_right.cons_tail
  clear sc37_l hc_csp
  -- 38. `match (*(chead)) { Const(_, _) => { () } };`
  obtain ⟨w_cha, w_chb, _, ld_chead, sc38, rest38⟩ :=
    invR_match_kexpr_const_unit (by rfl) sc37 rest37; clear sc37 rest37
  -- 39. `assert_eq!(Lists::length(cargs), cnp + ni)`
  obtain ⟨_, _, _, c39a, _, d39, mt39, rest39, hc39⟩ := rest38.letValue_inv; clear rest38
  rw [hc39] at sc38; have sc39_l := sc38.append_left; have sc39 := sc38.append_right; clear sc38 hc39
  obtain ⟨_, a39, ap39⟩ := d39.builtin_inv
  obtain ⟨v39_l, cnp_ni, h_clen, c39_l, _, rfl, hc39_args, d39_1, d39_2⟩ := invR_args2 a39
  obtain ⟨_, _, _, cs_clen, a39_c, ev_clen, hc_clen⟩ := d39_1.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_clen hc_clen
  obtain ⟨_, rfl, d39_v⟩ := invR_args1 a39_c
  obtain ⟨rfl, rfl, rfl⟩ := invR_var_find (by rfl) d39_v
  obtain ⟨_, _, _, _, _, d39_b1, d39_b2, op_cnp_ni, _⟩ := d39_2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d39_b1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d39_b2
  obtain ⟨heq39, rfl⟩ := Builtin.assertEq_inv ap39; subst v39_l
  obtain rfl := matchPattern_wildcard_inv mt39
  rw [hc39_args, hc_clen] at sc39_l
  have call_clen := sc39_l.append_left.append_right.cons_head
  clear sc39_l hc39_args hc_clen
  -- 40. `assert_eq!(defeq_list_ok(rc, Lists::take(Lists::drop(largs, rp), ni), Lists::drop(cargs, cnp), ctx), 1)`
  obtain ⟨_, h_deidx, _, c40a, _, d40, mt40, rest40, hc40⟩ := rest39.letValue_inv; clear rest39
  rw [hc40] at sc39; have sc40_l := sc39.append_left; have sc40 := sc39.append_right; clear sc39 hc40
  obtain ⟨_, a40, ap40⟩ := d40.builtin_inv
  obtain ⟨_, _, _, c40_l, _, rfl, hc40_args, d40_1, d40_2⟩ := invR_args2 a40
  obtain ⟨_, _, _, cs_deidx, a40_c, ev_deidx, hc_deidx⟩ := d40_1.call_inv
  rw [instanceName_plain_some] at ev_deidx hc_deidx
  obtain ⟨_, v_idxl, v_idxr, _, _, h_idxl, h_idxr, _, _, _, _, rfl, _, d40_c1, d40_c2, d40_c3, d40_c4⟩ :=
    invR_args4 a40_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d40_c1
  obtain ⟨_, _, _, cs_idxl, a40_tk, ev_idxl, _⟩ := d40_c2.call_inv
  rw [Obs.Names.n3863982424408310192] at ev_idxl
  obtain ⟨v_ldrop, _, h_ldrop, _, _, rfl, _, d40_dr1, d40_ni⟩ := invR_args2 a40_tk
  obtain ⟨_, _, _, cs_ldrop, a40_dr1, ev_ldrop, _⟩ := d40_dr1.call_inv
  rw [Obs.Names.n4825454920124213627] at ev_ldrop
  obtain ⟨_, _, _, _, _, rfl, _, d40_la, d40_rp⟩ := invR_args2 a40_dr1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d40_la
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d40_rp
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d40_ni
  obtain ⟨_, _, _, cs_idxr, a40_dr2, ev_idxr, _⟩ := d40_c3.call_inv
  rw [Obs.Names.n4825454920124213627] at ev_idxr
  obtain ⟨_, _, _, _, _, rfl, _, d40_ca, d40_cp⟩ := invR_args2 a40_dr2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d40_ca
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d40_cp
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d40_c4
  obtain ⟨rfl, rfl, _⟩ := d40_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap40
  obtain rfl := matchPattern_wildcard_inv mt40
  rw [hc40_args, hc_deidx] at sc40_l
  have sub_deidx := sc40_l.append_left.append_right.cons_tail
  clear sc40_l hc40_args hc_deidx
  -- 41a. `let ty_m = rename(ty_r, src, dst)`
  obtain ⟨ty_m, h_ty_m, _, c41ra, _, d41r, mt41r, rest41r, hc41r⟩ := rest40.letValue_inv; clear rest40
  rw [hc41r] at sc40; have sc41r_l := sc40.append_left; have sc41r := sc40.append_right; clear sc40 hc41r
  obtain ⟨_, _, _, cs_ty_m, a41r, ev_ty_m, hc_ty_m⟩ := d41r.call_inv
  rw [instanceName_plain_some] at ev_ty_m hc_ty_m
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d41r_1, d41r_2, d41r_3⟩ := invR_args3 a41r
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d41r_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d41r_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d41r_3
  obtain rfl := matchPattern_bind_inv mt41r
  rw [hc_ty_m] at sc41r_l
  have sub_ty_m := sc41r_l.append_right.cons_tail
  clear sc41r_l hc_ty_m
  -- 41b. `defeq_tele(rc, tty, ty_m, rp, (&(Lists::Node::Nil)))`
  obtain ⟨v_dt1, h_dt1, _, c41a, _, d41, mt41, rest41, hc41⟩ := rest41r.letValue_inv; clear rest41r
  rw [hc41] at sc41r; have sc41_l := sc41r.append_left; have sc41 := sc41r.append_right; clear sc41r hc41
  obtain ⟨_, _, _, cs_dt1, a41, ev_dt1, hc_dt1⟩ := d41.call_inv
  rw [instanceName_plain_some] at ev_dt1 hc_dt1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _,
    d41_1, d41_2, d41_3, d41_4, d41_5⟩ := invR_args5 a41
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d41_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d41_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d41_3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d41_4
  obtain ⟨rfl, rfl, _⟩ := invR_store_nil_kexpr d41_5
  obtain rfl := matchPattern_wildcard_inv mt41
  rw [hc_dt1] at sc41_l
  have sub_dt1 := sc41_l.append_right.cons_tail
  clear sc41_l hc_dt1
  -- 42. `defeq_tele(rc, KernelCheck::peel_n_foralls(tty, rp), crest, cnf, Lists::drop(ctx, cnf))`
  obtain ⟨v_dt2, h_dt2, _, c42a, _, d42, mt42, rest42, hc42⟩ := rest41.letValue_inv; clear rest41
  rw [hc42] at sc41; have sc42_l := sc41.append_left; have sc42 := sc41.append_right; clear sc41 hc42
  obtain ⟨_, h_ctx_rp, _, cs_dt2, a42, ev_dt2, hc_dt2⟩ := d42.call_inv
  rw [instanceName_plain_some] at ev_dt2 hc_dt2
  obtain ⟨_, v_tty_rp, _, _, v_ctx_rp, _, h_tty_rp, _, _, _, _, _, _, _, rfl, _,
    d42_1, d42_2, d42_3, d42_4, d42_5⟩ := invR_args5 a42
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d42_1
  obtain ⟨_, _, _, cs_tty_rp, a42_p, ev_tty_rp, _⟩ := d42_2.call_inv
  rw [instanceName_plain_some] at ev_tty_rp
  obtain ⟨_, _, _, _, _, rfl, _, d42_p1, d42_p2⟩ := invR_args2 a42_p
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d42_p1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d42_p2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d42_3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d42_4
  obtain ⟨_, _, _, cs_ctx_rp, a42_dr, ev_ctx_rp, _⟩ := d42_5.call_inv
  rw [Obs.Names.n4825454920124213627] at ev_ctx_rp
  obtain ⟨_, _, _, _, _, rfl, _, d42_dr1, d42_dr2⟩ := invR_args2 a42_dr
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d42_dr1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d42_dr2
  obtain rfl := matchPattern_wildcard_inv mt42
  rw [hc_dt2] at sc42_l
  have sub_dt2 := sc42_l.append_right.cons_tail
  clear sc42_l hc_dt2
  -- 43. `let (_, ctx_p) = peel_collect(ty_m, rp, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_ctxp, _, _, _, d43, mt43, rest43, hc43⟩ := rest42.letValue_inv; clear rest42
  rw [hc43] at sc42; have sc43 := sc42.append_right; clear sc42 hc43
  obtain ⟨_, _, _, cs_ctxp, a43, ev_ctxp, _⟩ := d43.call_inv
  rw [instanceName_plain_some] at ev_ctxp
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d43_1, d43_2, d43_3⟩ := invR_args3 a43
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d43_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d43_2
  obtain ⟨rfl, rfl, _⟩ := invR_store_nil_kexpr d43_3
  obtain ⟨_, hv43, -, ml43a⟩ := matchPattern_tuple_inv mt43; subst hv43
  obtain ⟨w_pbody, _, _, _, rfl, mt43_1, ml43b, rfl⟩ := matchListWith_cons_inv ml43a
  obtain rfl := matchPattern_wildcard_inv mt43_1
  obtain ⟨ctx_p, _, _, _, rfl, mt43_2, ml43c, rfl⟩ := matchListWith_cons_inv ml43b
  obtain rfl := matchPattern_bind_inv mt43_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml43c
  -- 44. `let crest_p = inst_params_typed(rc, rename(cty_l, src, dst), pins_ren, ctx_p)`
  obtain ⟨crest_p, h_crestp, _, c44a, _, d44, mt44, rest44, hc44⟩ := rest43.letValue_inv; clear rest43
  rw [hc44] at sc43; have sc44_l := sc43.append_left; have sc44 := sc43.append_right; clear sc43 hc44
  obtain ⟨_, _, _, cs_crestp, a44, ev_crestp, hc_crestp⟩ := d44.call_inv
  rw [instanceName_plain_some] at ev_crestp hc_crestp
  obtain ⟨_, v_cty_ren2, _, _, _, h_cty_ren2, _, _, c44_2, _, _, rfl, hc44_args,
    d44_1, d44_2, d44_3, d44_4⟩ := invR_args4 a44
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d44_1
  obtain ⟨_, _, _, cs_cty_ren2, a44_r, ev_cty_ren2, hc_cty_ren2⟩ := d44_2.call_inv
  rw [instanceName_plain_some] at ev_cty_ren2 hc_cty_ren2
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d44_r1, d44_r2, d44_r3⟩ := invR_args3 a44_r
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d44_r1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d44_r2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d44_r3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d44_3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d44_4
  obtain rfl := matchPattern_bind_inv mt44
  rw [hc_crestp, hc44_args, hc_cty_ren2] at sc44_l
  have sub_cty_ren2 := sc44_l.append_left.append_right.append_left.append_right.cons_tail
  have sub_crestp := sc44_l.append_right.cons_tail
  clear sc44_l hc_crestp hc44_args hc_cty_ren2
  -- 45. `let (rhs_rp, lctx) = defeq_lam_tele(rc, rhs_m, ty_m, rp, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_lt1, _, c45a, _, d45, mt45, rest45, hc45⟩ := rest44.letValue_inv; clear rest44
  rw [hc45] at sc44; have sc45_l := sc44.append_left; have sc45 := sc44.append_right; clear sc44 hc45
  obtain ⟨_, _, _, cs_lt1, a45, ev_lt1, hc_lt1⟩ := d45.call_inv
  rw [instanceName_plain_some] at ev_lt1 hc_lt1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _,
    d45_1, d45_2, d45_3, d45_4, d45_5⟩ := invR_args5 a45
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d45_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d45_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d45_3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d45_4
  obtain ⟨rfl, rfl, _⟩ := invR_store_nil_kexpr d45_5
  obtain ⟨_, hv45, -, ml45a⟩ := matchPattern_tuple_inv mt45; subst hv45
  obtain ⟨rhs_rp, _, _, _, rfl, mt45_1, ml45b, rfl⟩ := matchListWith_cons_inv ml45a
  obtain rfl := matchPattern_bind_inv mt45_1
  obtain ⟨lctx, _, _, _, rfl, mt45_2, ml45c, rfl⟩ := matchListWith_cons_inv ml45b
  obtain rfl := matchPattern_bind_inv mt45_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml45c
  rw [hc_lt1] at sc45_l
  have sub_lt1 := sc45_l.append_right.cons_tail
  clear sc45_l hc_lt1
  -- 46. `let (_, _) = defeq_lam_tele(rc, rhs_rp, crest_p, cnf, lctx)`
  obtain ⟨_, h_lt2, _, c46a, _, d46, mt46, rest46, hc46⟩ := rest45.letValue_inv; clear rest45
  rw [hc46] at sc45; have sc46_l := sc45.append_left; have sc46 := sc45.append_right; clear sc45 hc46
  obtain ⟨_, _, _, cs_lt2, a46, ev_lt2, hc_lt2⟩ := d46.call_inv
  rw [instanceName_plain_some] at ev_lt2 hc_lt2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _,
    d46_1, d46_2, d46_3, d46_4, d46_5⟩ := invR_args5 a46
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d46_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d46_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d46_3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d46_4
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d46_5
  obtain ⟨_, hv46, -, ml46a⟩ := matchPattern_tuple_inv mt46; subst hv46
  obtain ⟨w_lt2a, _, _, _, rfl, mt46_1, ml46b, rfl⟩ := matchListWith_cons_inv ml46a
  obtain rfl := matchPattern_wildcard_inv mt46_1
  obtain ⟨w_lt2b, _, _, _, rfl, mt46_2, ml46c, rfl⟩ := matchListWith_cons_inv ml46b
  obtain rfl := matchPattern_wildcard_inv mt46_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml46c
  rw [hc_lt2] at sc46_l
  have sub_lt2 := sc46_l.append_right.cons_tail
  clear sc46_l hc_lt2
  -- 47. `let rhs_app = KernelWhnf::apply_spine(rhs_m, bvars_desc(d, d))`
  obtain ⟨rhs_app, h_rhsapp, _, _, _, d47, mt47, rest47, hc47⟩ := rest46.letValue_inv; clear rest46
  rw [hc47] at sc46; have sc47 := sc46.append_right; clear sc46 hc47
  obtain ⟨_, h_bvd3, _, cs_rhsapp, a47, ev_rhsapp, _⟩ := d47.call_inv
  rw [instanceName_plain_some] at ev_rhsapp
  obtain ⟨_, v_bvd3, _, _, _, rfl, _, d47_1, d47_2⟩ := invR_args2 a47
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d47_1
  obtain ⟨_, _, _, cs_bvd3, a47_bv, ev_bvd3, _⟩ := d47_2.call_inv
  rw [instanceName_plain_some] at ev_bvd3
  obtain ⟨_, _, _, _, _, rfl, _, d47_bv1, d47_bv2⟩ := invR_args2 a47_bv
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d47_bv1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d47_bv2
  obtain rfl := matchPattern_bind_inv mt47
  -- 48. `assert_eq!(KernelDefEq::k_is_def_eq(rc, rhs_s, rhs_app, ctx), 1)`
  obtain ⟨_, h_derhs, _, c48a, _, d48, mt48, rest48, hc48⟩ := rest47.letValue_inv; clear rest47
  rw [hc48] at sc47; have sc48_l := sc47.append_left; have sc48 := sc47.append_right; clear sc47 hc48
  obtain ⟨_, a48, ap48⟩ := d48.builtin_inv
  obtain ⟨_, _, _, c48_l, _, rfl, hc48_args, d48_1, d48_2⟩ := invR_args2 a48
  obtain ⟨_, _, _, cs_derhs, a48_c, ev_derhs, hc_derhs⟩ := d48_1.call_inv
  rw [instanceName_plain_some] at ev_derhs hc_derhs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d48_c1, d48_c2, d48_c3, d48_c4⟩ := invR_args4 a48_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d48_c1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d48_c2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d48_c3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d48_c4
  obtain ⟨rfl, rfl, _⟩ := d48_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap48
  obtain rfl := matchPattern_wildcard_inv mt48
  rw [hc48_args, hc_derhs] at sc48_l
  have sub_derhs := sc48_l.append_left.append_right.cons_tail
  clear sc48_l hc48_args hc_derhs
  -- 49. `let tl = KernelInfer::k_infer(rc, lhs, ctx)`
  obtain ⟨tl, h_tl, _, c49a, _, d49, mt49, rest49, hc49⟩ := rest48.letValue_inv; clear rest48
  rw [hc49] at sc48; have sc49_l := sc48.append_left; have sc49 := sc48.append_right; clear sc48 hc49
  obtain ⟨_, _, _, cs_tl, a49, ev_tl, hc_tl⟩ := d49.call_inv
  rw [instanceName_plain_some] at ev_tl hc_tl
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d49_1, d49_2, d49_3⟩ := invR_args3 a49
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d49_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d49_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d49_3
  obtain rfl := matchPattern_bind_inv mt49
  rw [hc_tl] at sc49_l
  have sub_tl := sc49_l.append_right.cons_tail
  clear sc49_l hc_tl
  -- 50. `assert_eq!(KernelDefEq::k_is_def_eq(rc, tl, alpha, ctx), 1)`
  obtain ⟨_, h_detl, _, c50a, _, d50, mt50, rest50, hc50⟩ := rest49.letValue_inv; clear rest49
  rw [hc50] at sc49; have sc50_l := sc49.append_left; have sc50 := sc49.append_right; clear sc49 hc50
  obtain ⟨_, a50, ap50⟩ := d50.builtin_inv
  obtain ⟨_, _, _, c50_l, _, rfl, hc50_args, d50_1, d50_2⟩ := invR_args2 a50
  obtain ⟨_, _, _, cs_detl, a50_c, ev_detl, hc_detl⟩ := d50_1.call_inv
  rw [instanceName_plain_some] at ev_detl hc_detl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d50_c1, d50_c2, d50_c3, d50_c4⟩ := invR_args4 a50_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d50_c1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d50_c2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d50_c3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d50_c4
  obtain ⟨rfl, rfl, _⟩ := d50_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap50
  obtain rfl := matchPattern_wildcard_inv mt50
  rw [hc50_args, hc_detl] at sc50_l
  have sub_detl := sc50_l.append_left.append_right.cons_tail
  clear sc50_l hc50_args hc_detl
  -- 51. `let tr = KernelInfer::k_infer(rc, rhs_s, ctx)`
  obtain ⟨tr, h_tr, _, c51a, _, d51, mt51, rest51, hc51⟩ := rest50.letValue_inv; clear rest50
  rw [hc51] at sc50; have sc51_l := sc50.append_left; have sc51 := sc50.append_right; clear sc50 hc51
  obtain ⟨_, _, _, cs_tr, a51, ev_tr, hc_tr⟩ := d51.call_inv
  rw [instanceName_plain_some] at ev_tr hc_tr
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d51_1, d51_2, d51_3⟩ := invR_args3 a51
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d51_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d51_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d51_3
  obtain rfl := matchPattern_bind_inv mt51
  rw [hc_tr] at sc51_l
  have sub_tr := sc51_l.append_right.cons_tail
  clear sc51_l hc_tr
  -- 52. `assert_eq!(KernelDefEq::k_is_def_eq(rc, tr, alpha, ctx), 1)`
  obtain ⟨_, h_detr, _, c52a, _, d52, mt52, rest52, hc52⟩ := rest51.letValue_inv; clear rest51
  rw [hc52] at sc51; have sc52_l := sc51.append_left; have sc52 := sc51.append_right; clear sc51 hc52
  obtain ⟨_, a52, ap52⟩ := d52.builtin_inv
  obtain ⟨_, _, _, c52_l, _, rfl, hc52_args, d52_1, d52_2⟩ := invR_args2 a52
  obtain ⟨_, _, _, cs_detr, a52_c, ev_detr, hc_detr⟩ := d52_1.call_inv
  rw [instanceName_plain_some] at ev_detr hc_detr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d52_c1, d52_c2, d52_c3, d52_c4⟩ := invR_args4 a52_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d52_c1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d52_c2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d52_c3
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d52_c4
  obtain ⟨rfl, rfl, _⟩ := d52_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap52
  obtain rfl := matchPattern_wildcard_inv mt52
  rw [hc52_args, hc_detr] at sc52_l
  have sub_detr := sc52_l.append_left.append_right.cons_tail
  clear sc52_l hc52_args hc_detr
  -- 53. `let ta = KernelInfer::k_infer(rc, alpha, ctx)`
  obtain ⟨ta, h_ta, _, c53a, _, d53, mt53, rest53, hc53⟩ := rest52.letValue_inv; clear rest52
  rw [hc53] at sc52; have sc53_l := sc52.append_left; have sc53 := sc52.append_right; clear sc52 hc53
  obtain ⟨_, _, _, cs_ta, a53, ev_ta, hc_ta⟩ := d53.call_inv
  rw [instanceName_plain_some] at ev_ta hc_ta
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d53_1, d53_2, d53_3⟩ := invR_args3 a53
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d53_1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d53_2
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d53_3
  obtain rfl := matchPattern_bind_inv mt53
  rw [hc_ta] at sc53_l
  have sub_ta := sc53_l.append_right.cons_tail
  clear sc53_l hc_ta
  -- 54. `assert_eq!(KernelDefEq::k_is_def_eq(rc, ta, (&(KernelTypes::KExprNode::Srt(ell))), ctx), 1)`
  obtain ⟨_, h_deta, _, c54a, _, d54, _, _, hc54⟩ := rest53.letValue_inv; clear rest53
  rw [hc54] at sc53; have sc54_l := sc53.append_left; clear sc53 hc54
  obtain ⟨_, a54, ap54⟩ := d54.builtin_inv
  obtain ⟨_, _, _, c54_l, _, rfl, hc54_args, d54_1, d54_2⟩ := invR_args2 a54
  obtain ⟨_, _, _, cs_deta, a54_c, ev_deta, hc_deta⟩ := d54_1.call_inv
  rw [instanceName_plain_some] at ev_deta hc_deta
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d54_c1, d54_c2, d54_c3, d54_c4⟩ := invR_args4 a54_c
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d54_c1
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d54_c2
  obtain ⟨_, _, d54_srt, rfl, rfl⟩ := d54_c3.store_inv
  obtain ⟨_, a54_srt, hres54⟩ := d54_srt.construct_inv
  rw [instanceName_plain_some] at hres54; subst hres54
  obtain ⟨_, rfl, d54_ell⟩ := invR_args1 a54_srt
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d54_ell
  obtain ⟨rfl, rfl, _⟩ := invR_var_find (by rfl) d54_c4
  obtain ⟨rfl, rfl, _⟩ := d54_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap54
  simp only [Value.type] at ev_deta
  rw [hc54_args, hc_deta] at sc54_l
  have sub_deta := sc54_l.append_left.append_right.cons_tail
  subst hcalls₀_eq
  exact ⟨
    { mi := mi, d, op_mi, op_d, h_plen, cs_plen, call_plen, ev_plen,
      v_sc, h_sc, cs_sc, ev_sc, sub_sc,
      r_peel_e, r_peel_acc, h_peel, cs_peel, ev_peel,
      rhs_m, h_rhs_m, cs_rhs_m, ev_rhs_m, sub_rhs_m,
      v_rhs_ty, h_rhs_inf, cs_rhs_inf, ev_rhs_inf, sub_rhs_inf,
      h_aset, cs_aset, ev_aset, sub_aset,
      p_tci, h_tci, cs_tci, ev_tci, sub_tci, tty, w_tval, ld_tci,
      tbody, ctx, h_open, cs_open, ev_open,
      eqh, targs, h_tsp, cs_tsp, ev_tsp, eqa, eqls, ld_eqh,
      v_req, h_req, cs_req, v_raddr, h_raddr, cs_raddr, h_eqa, cs_eqa,
      ev_req, ev_raddr, sub_raddr, ev_eqa,
      ell, eqrest, ld_eqls1, ld_eqls2,
      h_tlen, cs_tlen, call_tlen, ev_tlen,
      alpha, lhs, rhs_s, h_a0, cs_a0, h_a1, cs_a1, h_a2, cs_a2, ev_a0, ev_a1, ev_a2,
      lh, largs, h_lsp, cs_lsp, ev_lsp,
      v_plvls, h_plvls, cs_plvls, ev_plvls,
      h_lheq, cs_lheq, ev_lheq,
      mi1, op_mi1, h_llen, cs_llen, call_llen, ev_llen,
      v_ltake, h_ltake, cs_ltake, v_bvd1, h_bvd1, cs_bvd1, h_pref, cs_pref,
      ev_ltake, ev_bvd1, ev_pref,
      major, h_maj, cs_maj, ev_maj,
      cren, h_cren, cs_cren, ev_cren,
      pins_ren, h_pren, cs_pren, ev_pren,
      pins_d, h_pd, cs_pd, ev_pd, sub_pd,
      v_bvd2, h_bvd2, cs_bvd2, v_cat, h_cat, cs_cat,
      expected, h_exp, cs_exp, h_majeq, cs_majeq,
      ev_bvd2, ev_cat, ev_exp, ev_majeq,
      cty_l, h_ctyl, cs_ctyl, ev_ctyl, sub_ctyl,
      cnp_cnf, op_cnp_cnf, v_peel0, h_peel0, cs_peel0,
      chead0, cargs0, h_csp0, cs_csp0, ev_peel0, ev_csp0, sub_csp0,
      w_ch0a, w_ch0b, ld_chead0,
      v_cty_ren, h_cty_ren, cs_cty_ren, crest, h_crest, cs_crest,
      ev_cty_ren, sub_cty_ren, ev_crest, sub_crest,
      cres, w_cctx, h_cres, cs_cres, ev_cres,
      chead, cargs, h_csp, cs_csp, ev_csp, sub_csp,
      w_cha, w_chb, ld_chead,
      cnp_ni, op_cnp_ni, h_clen, cs_clen, call_clen, ev_clen,
      v_ldrop, h_ldrop, cs_ldrop, v_idxl, h_idxl, cs_idxl, v_idxr, h_idxr, cs_idxr,
      h_deidx, cs_deidx, ev_ldrop, ev_idxl, ev_idxr, ev_deidx, sub_deidx,
      ty_m, h_ty_m, cs_ty_m, ev_ty_m, sub_ty_m, v_dt1, h_dt1, cs_dt1, ev_dt1, sub_dt1,
      v_tty_rp, h_tty_rp, cs_tty_rp, v_ctx_rp, h_ctx_rp, cs_ctx_rp,
      v_dt2, h_dt2, cs_dt2, ev_tty_rp, ev_ctx_rp, ev_dt2, sub_dt2,
      w_pbody, ctx_p, h_ctxp, cs_ctxp, ev_ctxp,
      v_cty_ren2, h_cty_ren2, cs_cty_ren2, ev_cty_ren2, sub_cty_ren2,
      crest_p, h_crestp, cs_crestp, ev_crestp, sub_crestp,
      rhs_rp, lctx, h_lt1, cs_lt1, ev_lt1, sub_lt1,
      w_lt2a, w_lt2b, h_lt2, cs_lt2, ev_lt2, sub_lt2,
      v_bvd3, h_bvd3, cs_bvd3,
      rhs_app, h_rhsapp, cs_rhsapp, h_derhs, cs_derhs,
      ev_bvd3, ev_rhsapp, ev_derhs, sub_derhs,
      tl, h_tl, cs_tl, h_detl, cs_detl, tr, h_tr, cs_tr, h_detr, cs_detr,
      ta, h_ta, cs_ta, h_deta, cs_deta,
      ev_tl, sub_tl, ev_detl, sub_detl, ev_tr, sub_tr, ev_detr, sub_detr,
      ev_ta, sub_ta, ev_deta, sub_deta }⟩

end IxVM.Refinement.Decl
