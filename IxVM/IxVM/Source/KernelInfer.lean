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

        KernelTypes::KExprNode::Lam(ty, body) => {
          k_ensure_sort(rc, ty, types);
          let types2 = (&(Lists::Node::Cons(ty, types)));
          let body_ty = k_infer(rc, body, types2);
          (&(KernelTypes::KExprNode::Forall(ty, body_ty))) } ,

        KernelTypes::KExprNode::Forall(ty, body) => {
          let u1 = k_ensure_sort(rc, ty, types);
          let types2 = (&(Lists::Node::Cons(ty, types)));
          let u2 = k_ensure_sort(rc, body, types2);
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
            KernelTypes::KExprNode::Forall(dom, cod) => {
              let dom_subst = inst_subs(dom, subs_rev);
              k_check(rc, a, dom_subst, types);
              k_infer_app_spine_loop(rc, cod, rest,
                (&(Lists::Node::Cons(a, subs_rev))), types) } ,
            _ => {
              let t_concrete = inst_subs(t, subs_rev);
              let t_w = KernelWhnf::whnf(rc, t_concrete, types);
              match (*(t_w)) {
                KernelTypes::KExprNode::Forall(dom, cod) => {
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
            KernelTypes::KExprNode::Forall(_, body) => {
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

  -- A positive certificate for a 0 answer of `level_equal(l, 0)` (RULES-GAP exact
  -- site 1): `l` is nonzero at some valuation (its zero-ness is not `ifAllZero []`).
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

  -- Infer.proj's shape premises (both grades): the structure has no indices (D5:
  -- `.proj` on an indexed family is rejected), the scrutinee's type has exactly the
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
            KernelTypes::KExprNode::Forall(dom, body) => {
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
        KernelTypes::KExprNode::Forall(dom, body) => {
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

def try_dec_dispatch := aiur_fn⟦
  fn try_dec_dispatch(rc: KernelRoles::RoleCtx, head_addr: Bytes::AddressRef, op: Field, head_lvls: Lists::List<KernelTypes::KLevel>,
                            spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>)
                            -> (Field, KernelTypes::KExpr) {
      match UInt32::less_than_fields(Lists::length(spine), 2) {
        1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {
          match op {
            1 => {  dec_rewrite_lt_to_le(rc, spine, types) } ,
            2 => {  dec_nat(rc, 1, head_addr, head_lvls, spine, types) } ,
            3 => {  dec_nat(rc, 0, head_addr, head_lvls, spine, types) } ,
            4 => {  dec_rewrite_int_lt_to_le(rc, spine, types) } ,
            5 => {  dec_int(rc, 1, head_addr, head_lvls, spine, types) } ,
            6 => {  dec_int(rc, 0, head_addr, head_lvls, spine, types) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

def dec_rewrite_lt_to_le := aiur_fn⟦
  fn dec_rewrite_lt_to_le(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>,
                             types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let n_e = Lists::lookup(spine, 0);
      let m_e = Lists::lookup(spine, 1);
      let n_w = KernelWhnf::whnf(rc, n_e, types);
      match KernelNatPrim::try_extract_nat(rc, n_w) {
        (0, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        (1, n_klimbs) => {
          let succ_lit = KernelNatPrim::mk_nat_lit(KernelKlimbs::klimbs_succ(n_klimbs));
          let dec_le_head = (&(KernelTypes::KExprNode::Const(
            KernelRoles::role_addr(rc, KernelRoleSpec::role_nat_dec_le()), (&(Lists::Node::Nil)))));
          let app1 = (&(KernelTypes::KExprNode::App(dec_le_head, succ_lit)));
          let app2 = (&(KernelTypes::KExprNode::App(app1, m_e)));
          let post = Lists::drop(spine, 2);
          (1, KernelWhnf::apply_spine(app2, post)) } ,
      }
    }
⟧

def dec_nat := aiur_fn⟦
  fn dec_nat(rc: KernelRoles::RoleCtx, is_le: Field, head_addr: Bytes::AddressRef, head_lvls: Lists::List<KernelTypes::KLevel>,
                spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let n_e = Lists::lookup(spine, 0);
      let m_e = Lists::lookup(spine, 1);
      let n_w = KernelWhnf::whnf(rc, n_e, types);
      let m_w = KernelWhnf::whnf(rc, m_e, types);
      match KernelNatPrim::try_extract_nat(rc, n_w) {
        (0, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        (1, n_kl) => {
          match KernelNatPrim::try_extract_nat(rc, m_w) {
            (0, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
            (1, m_kl) => {
              let verdict = match is_le {
                1 => {  KernelKlimbs::klimbs_le(n_kl, m_kl) } ,
                _ => {  KernelLevels::klimbs_eq(n_kl, m_kl) } ,
              };
              let prop = match is_le {
                1 => {
                  let le_c = (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_nat_le()),
                    (&(Lists::Node::Nil)))));
                  (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(le_c, n_e))), m_e))) } ,
                _ => {  mk_eq1(rc, (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat()),
                    (&(Lists::Node::Nil))))), n_e, m_e) } ,
              };
              let call = (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(
                (&(KernelTypes::KExprNode::Const(head_addr, head_lvls))), n_e))), m_e)));
              (1, KernelWhnf::apply_spine(dec_result(rc, verdict, prop, call), Lists::drop(spine, 2))) } ,
          } } ,
      }
    }
⟧

def dec_rewrite_int_lt_to_le := aiur_fn⟦
  fn dec_rewrite_int_lt_to_le(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>,
                                 types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let a_e = Lists::lookup(spine, 0);
      let b_e = Lists::lookup(spine, 1);
      let a_w = KernelWhnf::whnf(rc, a_e, types);
      match KernelNatPrim::try_extract_int_prim(rc, a_w) {
        (0, _, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        (1, sa, na) => {
          let one = (&(Lists::Node::Cons([UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0],
            (&(Lists::Node::Nil)))));
          let succ_a = KernelNatPrim::int_add_prim(rc, sa, na, 0, one);
          let dec_le_head = (&(KernelTypes::KExprNode::Const(
            KernelRoles::role_addr(rc, KernelRoleSpec::role_int_dec_le()), (&(Lists::Node::Nil)))));
          let app2 = (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(dec_le_head, succ_a))), b_e)));
          (1, KernelWhnf::apply_spine(app2, Lists::drop(spine, 2))) } ,
      }
    }
⟧

def dec_int := aiur_fn⟦
  fn dec_int(rc: KernelRoles::RoleCtx, is_le: Field, head_addr: Bytes::AddressRef, head_lvls: Lists::List<KernelTypes::KLevel>,
                spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let a_e = Lists::lookup(spine, 0);
      let b_e = Lists::lookup(spine, 1);
      let a_w = KernelWhnf::whnf(rc, a_e, types);
      let b_w = KernelWhnf::whnf(rc, b_e, types);
      match KernelNatPrim::try_extract_int_prim(rc, a_w) {
        (0, _, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        (1, sa, na) => {
          match KernelNatPrim::try_extract_int_prim(rc, b_w) {
            (0, _, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
            (1, sb, nb) => {
              let verdict = match is_le {
                1 => {  int_le_verdict(sa, na, sb, nb) } ,
                _ => {  (1 - (sa - sb) * (sa - sb)) * KernelLevels::klimbs_eq(na, nb) } ,
              };
              let prop = match is_le {
                1 => {
                  let le_c = (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_int_le()),
                    (&(Lists::Node::Nil)))));
                  (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(le_c, a_e))), b_e))) } ,
                _ => {  mk_eq1(rc, (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_int()),
                    (&(Lists::Node::Nil))))), a_e, b_e) } ,
              };
              let call = (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(
                (&(KernelTypes::KExprNode::Const(head_addr, head_lvls))), a_e))), b_e)));
              (1, KernelWhnf::apply_spine(dec_result(rc, verdict, prop, call), Lists::drop(spine, 2))) } ,
          } } ,
      }
    }
⟧

def int_le_verdict := aiur_fn⟦
  fn int_le_verdict(sa: Field, na: KernelTypes::KLimbs, sb: Field, nb: KernelTypes::KLimbs) -> Field {
      match sa {
        0 => {  match sb { 0 => {  KernelKlimbs::klimbs_le(na, nb) } , _ => {  0 } , } } ,
        _ => {  match sb { 0 => {  1 } , _ => {  KernelKlimbs::klimbs_le(nb, na) } , } } ,
      }
    }
⟧

def mk_eq1 := aiur_fn⟦
  fn mk_eq1(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, a: KernelTypes::KExpr, b: KernelTypes::KExpr) -> KernelTypes::KExpr {
      let one_lvl = (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))));
      let eq_c = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_eq()),
        (&(Lists::Node::Cons(one_lvl, (&(Lists::Node::Nil))))))));
      (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(eq_c, ty))), a))), b)))
    }
⟧

def dec_result := aiur_fn⟦
  fn dec_result(rc: KernelRoles::RoleCtx, verdict: Field, prop: KernelTypes::KExpr, call: KernelTypes::KExpr) -> KernelTypes::KExpr {
      let one_lvl = (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))));
      let eq_refl_c = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_eq_refl()),
        (&(Lists::Node::Cons(one_lvl, (&(Lists::Node::Nil))))))));
      let bool_c = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_bool()), (&(Lists::Node::Nil)))));
      let refl = (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(eq_refl_c, bool_c))), KernelNatPrim::mk_bool(rc, verdict))));
      let of_decide = match verdict {
        1 => {  KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_of_decide_eq_true()) } ,
        _ => {  KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_of_decide_eq_false()) } ,
      };
      let ctor = match verdict {
        1 => {  KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_decidable_is_true()) } ,
        _ => {  KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_decidable_is_false()) } ,
      };
      let proof = (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(
        (&(KernelTypes::KExprNode::Const(of_decide, (&(Lists::Node::Nil))))), prop))), call))), refl)));
      (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(
        (&(KernelTypes::KExprNode::Const(ctor, (&(Lists::Node::Nil))))), prop))), proof)))
    }
⟧

def try_str_dec_eq := aiur_fn⟦
  fn try_str_dec_eq(rc: KernelRoles::RoleCtx, head_addr: Bytes::AddressRef, spine: Lists::List<KernelTypes::KExpr>,
                          types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match UInt32::less_than_fields(Lists::length(spine), 2) {
        1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {
          let a0 = Lists::lookup(spine, 0);
          let a1 = Lists::lookup(spine, 1);
          match (*(a0)) {
            KernelTypes::KExprNode::Lit(la) => {
              match la {
                KernelTypes::KLiteral::Str(sa) => {
                  match (*(a1)) {
                    KernelTypes::KExprNode::Lit(lb) => {
                      match lb {
                        KernelTypes::KLiteral::Str(sb) => {
                          match KernelLevels::bytestream_eq(sa, sb) {
                            0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                            _ => {
                              let str_c = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_string()),
                                (&(Lists::Node::Nil)))));
                              let call = (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::App(
                                (&(KernelTypes::KExprNode::Const(head_addr, (&(Lists::Node::Nil))))), a0))), a1)));
                              (1, KernelWhnf::apply_spine(dec_result(rc, 1, mk_eq1(rc, str_c, a0, a1), call),
                                Lists::drop(spine, 2))) } ,
                          } } ,
                        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                      } } ,
                    _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                  } } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

end

end IxVM
