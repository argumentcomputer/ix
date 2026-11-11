import Aiur.Modules.Function

/-! # IxVM module `KernelInfer`

Type inference.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelInfer where

def types_lookup := aiur_fn⟦
  fn types_lookup(types: Lists::List<KernelTypes::KExpr>, i: Field) -> KernelTypes::KExpr {
      let ty = Lists::lookup(types, i);
      KernelSubst::expr_lift(ty, i + 1, 0)
    }
⟧

def const_num_lvls := aiur_fn⟦
  fn const_num_lvls(ci: KernelTypes::KConstantInfo) -> Field {
      match ci {
        KernelTypes::KConstantInfo::Axiom(n, _, _) => {  n } ,
        KernelTypes::KConstantInfo::Defn(n, _, _, _, _) => {  n } ,
        KernelTypes::KConstantInfo::Thm(n, _, _) => {  n } ,
        KernelTypes::KConstantInfo::Opaque(n, _, _, _) => {  n } ,
        KernelTypes::KConstantInfo::Quot(n, _, _) => {  n } ,
        KernelTypes::KConstantInfo::Induct(n, _, _, _, _, _, _, _) => {  n } ,
        KernelTypes::KConstantInfo::Ctor(n, _, _, _, _, _, _, _) => {  n } ,
        KernelTypes::KConstantInfo::Rec(n, _, _, _, _, _, _, _, _, _, _) => {  n } ,
      }
    }
⟧

def const_type_of := aiur_fn⟦
  fn const_type_of(ci: KernelTypes::KConstantInfo) -> KernelTypes::KExpr {
      match ci {
        KernelTypes::KConstantInfo::Axiom(_, ty, _) => {  ty } ,
        KernelTypes::KConstantInfo::Defn(_, ty, _, _, _) => {  ty } ,
        KernelTypes::KConstantInfo::Thm(_, ty, _) => {  ty } ,
        KernelTypes::KConstantInfo::Opaque(_, ty, _, _) => {  ty } ,
        KernelTypes::KConstantInfo::Quot(_, ty, _) => {  ty } ,
        KernelTypes::KConstantInfo::Induct(_, ty, _, _, _, _, _, _) => {  ty } ,
        KernelTypes::KConstantInfo::Ctor(_, ty, _, _, _, _, _, _) => {  ty } ,
        KernelTypes::KConstantInfo::Rec(_, ty, _, _, _, _, _, _, _, _, _) => {  ty } ,
      }
    }
⟧

def k_infer := aiur_fn⟦
  fn k_infer(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let base = KernelSubst::expr_lbr(e);
      match base {
        0 => {  k_infer_core(rc, e, (&(Lists::Node::Nil))) } ,
        _ => {  k_infer_rebase(rc, e, types, base) } ,
      }
    }
⟧

def k_infer_rebase := aiur_fn⟦
  fn k_infer_rebase(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>, base: Field) -> KernelTypes::KExpr {
      let g = KernelSubst::lbr_min(KernelSubst::expr_glb(e, 0), Lists::length(types));
      match g {
        0 => {  k_infer_core(rc, e, KernelSubst::ctx_trim(types, base)) } ,
        _ => {
          let t = k_infer_core(rc, KernelSubst::expr_lower(e, g, 0),
                      KernelSubst::ctx_trim(Lists::drop(types, g), base - g));
          KernelSubst::expr_lift(t, g, 0) } ,
      }
    }
⟧

def k_infer_core := aiur_fn⟦
  fn k_infer_core(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(i) => {  types_lookup(types, i) } ,

        KernelTypes::KExprNode::Srt(l) => {
          (&(KernelTypes::KExprNode::Srt(KernelLevels::level_reduce((&(KernelTypes::KLevelNode::Succ(l))))))) } ,

        KernelTypes::KExprNode::Const(addr, lvls) => {
          let ci = (*(Ingress::get_ci(addr)));
          let expected = const_num_lvls(ci);
          let given = Lists::length(lvls);
          assert_eq!(given, expected,
            "Const applied to wrong number of universe levels");
          let ty = const_type_of(ci);
          KernelLevels::expr_inst_levels(ty, lvls) } ,

        KernelTypes::KExprNode::App(_, _) => {
          match KernelTypes::collect_spine(e) {
            (head, args) => {
              let head_ty = k_infer(rc, head, types);
              k_infer_app_spine_loop(rc, head_ty, args, (&(Lists::Node::Nil)), types) } ,
          } } ,

        KernelTypes::KExprNode::Lam(ty, body, bl) => {
          k_ensure_sort(rc, ty, types);
          let types2 = (&(Lists::Node::Cons(ty, types)));
          let body_ty = k_infer(rc, body, types2);
          KernelInferOnly::lam_datum_ok(rc, body, body_ty, bl, types2);
          (&(KernelTypes::KExprNode::Forall(ty, body_ty, bl))) } ,

        KernelTypes::KExprNode::Forall(ty, body, bl) => {
          let u1 = k_ensure_sort(rc, ty, types);
          let types2 = (&(Lists::Node::Cons(ty, types)));
          let u2 = k_ensure_sort(rc, body, types2);
          KernelInferOnly::forall_datum_ok(u2, bl);
          (&(KernelTypes::KExprNode::Srt(KernelLevels::level_imax(u1, u2)))) } ,

        KernelTypes::KExprNode::Let(ty, val, body) => {  k_infer_let_start(rc, ty, val, body, types) } ,

        KernelTypes::KExprNode::Lit(lit) => {  k_infer_lit(rc, lit) } ,
        KernelTypes::KExprNode::Proj(struct_addr, fidx, e1) => {
          k_infer_proj(rc, struct_addr, fidx, e1, types) } ,
      }
    }
⟧

def k_infer_let_start := aiur_fn⟦
  fn k_infer_let_start(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr,
                              types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      k_ensure_sort(rc, ty, types);
      k_check(rc, val, ty, types);
      k_infer(rc, KernelSubst::expr_inst1(body, val, 0), types)
    }
⟧

  -- The delayed substitution of an application spine (no list length is read as a
  -- field element: the empty substitution is matched structurally).

def inst_subs := aiur_fn⟦
  inline fn inst_subs(e: KernelTypes::KExpr, subs_rev: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(subs_rev)) {
        Lists::Node::Nil => {  e } ,
        Lists::Node::Cons(_, _) => {  KernelSubst::expr_inst_many(e, subs_rev, 0) } ,
      }
    }
⟧

def k_infer_app_spine_loop := aiur_fn⟦
  fn k_infer_app_spine_loop(rc: KernelRoles::RoleCtx, t: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>,
                                  subs_rev: Lists::List<KernelTypes::KExpr>,
                                  types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(args)) {
        Lists::Node::Nil => {
          inst_subs(t, subs_rev) } ,
        Lists::Node::Cons(a, rest) => {
          match (*(t)) {
            KernelTypes::KExprNode::Forall(dom, cod, _) => {
              let dom_subst = inst_subs(dom, subs_rev);
              k_check(rc, a, dom_subst, types);
              k_infer_app_spine_loop(rc, cod, rest,
                (&(Lists::Node::Cons(a, subs_rev))), types) } ,
            _ => {
              let t_concrete = inst_subs(t, subs_rev);
              let t_w = KernelWhnf::whnf(rc, t_concrete, types);
              match (*(t_w)) {
                KernelTypes::KExprNode::Forall(dom, cod, _) => {
                  k_check(rc, a, dom, types);
                  k_infer_app_spine_loop(rc, cod, rest,
                    (&(Lists::Node::Cons(a, (&(Lists::Node::Nil))))), types) } ,
              } } ,
          } } ,
      }
    }
⟧

def k_infer_lit := aiur_fn⟦
  fn k_infer_lit(rc: KernelRoles::RoleCtx, lit: KernelTypes::KLiteral) -> KernelTypes::KExpr {
      match lit {
        KernelTypes::KLiteral::Nat(_) => {  (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat()), (&(Lists::Node::Nil))))) } ,
        KernelTypes::KLiteral::Str(_) => {
          (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_string()), (&(Lists::Node::Nil))))) } ,
      }
    }
⟧

def peel_params_subst := aiur_fn⟦
  fn peel_params_subst(ty: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>, n_params: Field) -> KernelTypes::KExpr {
      match n_params {
        0 => {  ty } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(_, body, _) => {
              match (*(args)) {
                Lists::Node::Cons(arg, rest) => {
                  let body_substed = KernelSubst::expr_inst1(body, arg, 0);
                  peel_params_subst(body_substed, rest, n_params - 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def is_inductive_prop := aiur_fn⟦
  fn is_inductive_prop(rc: KernelRoles::RoleCtx, ind_ty: KernelTypes::KExpr, lvls: Lists::List<KernelTypes::KLevel>, n_skip: Field,
                              types: Lists::List<KernelTypes::KExpr>) -> Field {
      let ind_ty_inst = KernelLevels::expr_inst_levels(ind_ty, lvls);
      let result = peel_n_alls_whnf(rc, ind_ty_inst, n_skip, types);

      match (*(result)) {
        KernelTypes::KExprNode::Srt(l) => {
          match KernelLevels::level_equal(l, (&(KernelTypes::KLevelNode::Zero))) {
            1 => {  1 } ,
            _ => {
              assert_eq!(level_may_be_nonzero(l), 1,
                "projection: the structure's sort is zero, but not recognized as zero");
              0 } ,
          } } ,
      }
    }
⟧

  -- A positive certificate for a 0 answer of `level_equal(l, 0)`: `l` is nonzero at
  -- some valuation (its zero-ness is not `ifAllZero []`).
  -- With it, "the structure is data" is a fact, not an absence of proof.

def level_may_be_nonzero := aiur_fn⟦
  fn level_may_be_nonzero(l: KernelTypes::KLevel) -> Field {
      match (*(l)) {
        KernelTypes::KLevelNode::Zero => {  0 } ,
        KernelTypes::KLevelNode::Succ(_) => {  1 } ,
        KernelTypes::KLevelNode::Param(_) => {  1 } ,
        KernelTypes::KLevelNode::Max(a, b) => {
          match level_may_be_nonzero(a) {
            1 => {  1 } ,
            _ => {  level_may_be_nonzero(b) } ,
          } } ,
        KernelTypes::KLevelNode::IMax(_, b) => {  level_may_be_nonzero(b) } ,
      }
    }
⟧

  -- Infer.proj's shape premises (both grades): the structure has no indices
  -- (`.proj` on an indexed family is rejected), the scrutinee's type has exactly the
  -- structure's parameters, and its level list has the structure's length.

def proj_shape_ok := aiur_fn⟦
  fn proj_shape_ok(n_indices: Field, args: Lists::List<KernelTypes::KExpr>, n_params: Field,
                   lvls: Lists::List<KernelTypes::KLevel>, n_lvls: Field) -> () {
      assert_eq!(n_indices, 0, "projection on an indexed family");
      assert_eq!(Lists::length(args), n_params, "projection: the structure type's argument count");
      assert_eq!(Lists::length(lvls), n_lvls, "projection: the structure type's level count");
      ()
    }
⟧

def peel_n_alls_whnf := aiur_fn⟦
  fn peel_n_alls_whnf(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, n: Field, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match n {
        0 => {  KernelWhnf::whnf(rc, e, types) } ,
        _ => {
          let ew = KernelWhnf::whnf(rc, e, types);
          match (*(ew)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              let t2 = (&(Lists::Node::Cons(dom, types)));
              peel_n_alls_whnf(rc, body, n - 1, t2) } ,
            _ => {  ew } ,
          } } ,
      }
    }
⟧

def check_prop_field_if_prop := aiur_fn⟦
  fn check_prop_field_if_prop(rc: KernelRoles::RoleCtx, is_prop: Field, dom: KernelTypes::KExpr,
                                     types: Lists::List<KernelTypes::KExpr>) -> () {
      match is_prop {
        0 => {  () } ,
        _ => {
          let lvl = k_ensure_sort(rc, dom, types);
          assert_eq!(KernelLevels::level_equal(lvl, (&(KernelTypes::KLevelNode::Zero))), 1,
            "projection on a Prop structure: field is not a Prop");
          () } ,
      }
    }
⟧

def check_no_dep_data_field_if_prop := aiur_fn⟦
  fn check_no_dep_data_field_if_prop(rc: KernelRoles::RoleCtx, is_prop: Field, dom: KernelTypes::KExpr, body: KernelTypes::KExpr,
                                            types: Lists::List<KernelTypes::KExpr>) -> () {
      match is_prop {
        0 => {  () } ,
        _ => {
          let lvl = k_ensure_sort(rc, dom, types);
          match KernelLevels::level_equal(lvl, (&(KernelTypes::KLevelNode::Zero))) {
            1 => {  () } ,
            _ => {

              assert_eq!(KernelSubst::expr_lbr(body), 0,
                "projection on a Prop structure: later fields depend on a data field");
              () } ,
          } } ,
      }
    }
⟧

def peel_field_loop := aiur_fn⟦
  fn peel_field_loop(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, target: Field, current: Field,
                           struct_addr: Bytes::AddressRef, val: KernelTypes::KExpr, is_prop: Field,
                           types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          match target - current {
            0 => {
              check_prop_field_if_prop(rc, is_prop, dom, types);
              dom } ,
            _ => {
              check_no_dep_data_field_if_prop(rc, is_prop, dom, body, types);
              let proj_expr = (&(KernelTypes::KExprNode::Proj(struct_addr, current, val)));
              let body_substed = KernelSubst::expr_inst1(body, proj_expr, 0);
              peel_field_loop(rc, body_substed, target, current + 1,
                                   struct_addr, val, is_prop, types) } ,
          } } ,
      }
    }
⟧

def k_infer_proj := aiur_fn⟦
  fn k_infer_proj(rc: KernelRoles::RoleCtx, struct_addr: Bytes::AddressRef, fidx: Field, e1: KernelTypes::KExpr,
                        types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let val_ty = k_infer(rc, e1, types);
      let wty = KernelWhnf::whnf(rc, val_ty, types);
      match KernelTypes::collect_spine(wty) {
        (head, args) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(head_addr, lvls) => {
              assert_eq!(Bytes::address_eq(head_addr, struct_addr), 1,
                "projection's structure type differs from the value's head");
              let ind_ci = (*(Ingress::get_ci(head_addr)));
              match ind_ci {
                KernelTypes::KConstantInfo::Induct(ind_nlvls, ind_ty, n_params, n_indices, num_ctors, _,
                                       block_addr, ind_idx) => {

                  assert_eq!(num_ctors, 1,
                    "projection on an inductive with more than one constructor");
                  proj_shape_ok(n_indices, args, n_params, lvls, ind_nlvls);
                  let ctor_ci = (*(KernelModeled::proj_ctor(block_addr, ind_idx)));
                  match ctor_ci {
                    KernelTypes::KConstantInfo::Ctor(ctor_nlvls, ctor_ty, _, _, _, _, _, _) => {
                      assert_eq!(ctor_nlvls, ind_nlvls,
                        "projection's constructor universe count differs from its inductive's");
                      let ctor_ty_inst = KernelLevels::expr_inst_levels(ctor_ty, lvls);
                      let after_params = peel_params_subst(ctor_ty_inst, args, n_params);

                      let is_prop = is_inductive_prop(rc, ind_ty, lvls,
                                      n_params + n_indices, types);
                      peel_field_loop(rc, after_params, fidx, 0,
                                           struct_addr, e1, is_prop, types) } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def k_ensure_sort := aiur_fn⟦
  fn k_ensure_sort(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KLevel {
      let t = k_infer(rc, e, types);
      let tw = KernelWhnf::whnf(rc, t, types);
      match (*(tw)) {
        KernelTypes::KExprNode::Srt(l) => {  l } ,
      }
    }
⟧

def k_check := aiur_fn⟦
  fn k_check(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, expected: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> () {
      let inferred = k_infer(rc, e, types);
      let d = KernelDefEq::k_is_def_eq(rc, inferred, expected, types);
      assert_eq!(d, 1, "inferred type is not def-eq to the expected type");
    }
⟧










end

end IxVM
