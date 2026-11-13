import Aiur.Modules.Function

/-! # IxVM module `KernelInferOnly`

Inference without checking.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelInferOnly where

def io_types_lookup := aiur_fn⟦
  inline fn io_types_lookup(types: Lists::List<KernelTypes::KExpr>, i: Field) -> KernelTypes::KExpr {
      let ty = Lists::lookup(types, i);
      KernelSubst::expr_lift(ty, i + 1, 0)
    }
⟧

def io_const_num_lvls := aiur_fn⟦
  fn io_const_num_lvls(ci: KernelTypes::KConstantInfo) -> Field {
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

def io_const_type_of := aiur_fn⟦
  fn io_const_type_of(ci: KernelTypes::KConstantInfo) -> KernelTypes::KExpr {
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

def k_infer_only := aiur_fn⟦
  fn k_infer_only(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      k_infer_only_core(rc, e, KernelSubst::ctx_trim(types, KernelSubst::expr_lbr(e)))
    }
⟧

def k_infer_only_core := aiur_fn⟦
  inline fn k_infer_only_core(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(i) => {  io_types_lookup(types, i) } ,

        KernelTypes::KExprNode::Srt(l) => {
          (&(KernelTypes::KExprNode::Srt(KernelLevels::level_reduce((&(KernelTypes::KLevelNode::Succ(l))))))) } ,

        KernelTypes::KExprNode::Const(addr, lvls) => {
          let ci = (*(Ingress::get_ci(addr)));
          let expected = io_const_num_lvls(ci);
          assert_eq!(Lists::length(lvls), expected,
            "Const applied to wrong number of universe levels");
          let ty = io_const_type_of(ci);
          KernelLevels::expr_inst_levels(ty, lvls) } ,

        KernelTypes::KExprNode::App(f, a) => {
          let f_ty = k_infer_only(rc, f, types);
          match (*(f_ty)) {
            KernelTypes::KExprNode::Forall(dom, cod, bl) => {  io_app_cod(rc, dom, cod, bl, a, types) } ,
            _ => {
              let f_ty_whnf = KernelWhnf::whnf(rc, f_ty, types);
              match (*(f_ty_whnf)) {
                KernelTypes::KExprNode::Forall(dom, cod, bl) => {  io_app_cod(rc, dom, cod, bl, a, types) } ,
              } } ,
          } } ,

        KernelTypes::KExprNode::Lam(ty, body, bl) => {
          let types2 = (&(Lists::Node::Cons(ty, types)));
          let body_ty = k_infer_only(rc, body, types2);
          lam_datum_ok(rc, body, body_ty, bl, types2);
          (&(KernelTypes::KExprNode::Forall(ty, body_ty, bl))) } ,

        KernelTypes::KExprNode::Forall(ty, body, bl) => {
          let u1 = ensure_sort_only(rc, ty, types);
          let types2 = (&(Lists::Node::Cons(ty, types)));
          let u2 = ensure_sort_only(rc, body, types2);
          forall_datum_ok(u2, bl);
          (&(KernelTypes::KExprNode::Srt(KernelLevels::level_imax(u1, u2)))) } ,

        KernelTypes::KExprNode::Let(_, val, body) => {
          let body_substed = KernelSubst::expr_inst1(body, val, 0);
          k_infer_only(rc, body_substed, types) } ,

        KernelTypes::KExprNode::Lit(lit) => {
          match lit {
            KernelTypes::KLiteral::Nat(_) => {
              (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat()), (&(Lists::Node::Nil))))) } ,
            KernelTypes::KLiteral::Str(_) => {
              (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_string()), (&(Lists::Node::Nil))))) } ,
          } } ,

        KernelTypes::KExprNode::Proj(struct_addr, fidx, e1) => {
          let val_ty = k_infer_only(rc, e1, types);
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
                      KernelInfer::proj_shape_ok(n_indices, args, n_params, lvls, ind_nlvls);
                      let ctor_ci = (*(KernelModeled::proj_ctor(block_addr, ind_idx)));
                      match ctor_ci {
                        KernelTypes::KConstantInfo::Ctor(ctor_nlvls, ctor_ty, _, _, _, _, _, _) => {
                          assert_eq!(ctor_nlvls, ind_nlvls,
                            "projection's constructor universe count differs from its inductive's");
                          let ctor_ty_inst = KernelLevels::expr_inst_levels(ctor_ty, lvls);
                          let after_params = io_peel_params_subst(ctor_ty_inst, args, n_params);
                          KernelInfer::peel_field_loop(rc, after_params, fidx, 0, struct_addr, e1,
                            KernelInfer::is_inductive_prop(rc, ind_ty, lvls, n_params, types), types) } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Infer.forallE's datum premise (both grades): the binder's datum is the zero-ness of
  -- the body's sort (`zeronessOf v = mb.pw`).

  -- Infer.appSkip and Infer.app at the io grade: at a ∀ whose datum is never, no argument
  -- certificate; otherwise the argument's io-grade type is definitionally equal to the domain.

def io_app_cod := aiur_fn⟦
  inline fn io_app_cod(rc: KernelRoles::RoleCtx, dom: KernelTypes::KExpr, cod: KernelTypes::KExpr, bl: KernelTypes::KLevel,
                a: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match KernelLevels::level_is_not_zero(bl) {
        1 => {  KernelSubst::expr_inst1(cod, a, 0) } ,
        _ => {
          assert_eq!(KernelDefEq::k_is_def_eq(rc, k_infer_only(rc, a, types), dom, types), 1,
            "io application: the argument's type is not the domain");
          KernelSubst::expr_inst1(cod, a, 0) } ,
      }
    }
⟧

def forall_datum_ok := aiur_fn⟦
  inline fn forall_datum_ok(v: KernelTypes::KLevel, bl: KernelTypes::KLevel) -> () {
      assert_eq!(KernelLevels::pw_eq(v, bl), 1, "a binder's datum is not its codomain sort's zero-ness");
      ()
    }
⟧

  -- Infer.lam's datum premises (both grades), once per λ-chain: at a λ whose body is a
  -- λ, the two data agree; at the innermost λ, the datum is the zero-ness of the sort of
  -- the body's type, computed at the io grade.

def lam_datum_ok := aiur_fn⟦
  inline fn lam_datum_ok(rc: KernelRoles::RoleCtx, body: KernelTypes::KExpr, body_ty: KernelTypes::KExpr,
                         bl: KernelTypes::KLevel, types2: Lists::List<KernelTypes::KExpr>) -> () {
      match (*(body)) {
        KernelTypes::KExprNode::Lam(_, _, inner) => {
          assert_eq!(KernelLevels::pw_eq(bl, inner), 1, "a lambda's datum differs from its inner lambda's");
          () } ,
        _ => {
          assert_eq!(KernelLevels::pw_eq(ensure_sort_only(rc, body_ty, types2), bl), 1,
            "a lambda's datum is not the zero-ness of its body type's sort");
          () } ,
      }
    }
⟧

def ensure_sort_only := aiur_fn⟦
  fn ensure_sort_only(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KLevel {
      let ty = k_infer_only(rc, e, types);
      match (*(ty)) {
        KernelTypes::KExprNode::Srt(l) => {  l } ,
        _ => {
          let ty_whnf = KernelWhnf::whnf(rc, ty, types);
          match (*(ty_whnf)) {
            KernelTypes::KExprNode::Srt(l) => {  l } ,
          } } ,
      }
    }
⟧

  -- Infer.proj's `FireSem` premise at the io grade: at a `Prop`
  -- structure the projected field's type is a proposition. (Full inference runs the
  -- same guard in `k_infer_proj`; the io grade used to rely on that earlier run.)

def io_prop_field_guard := aiur_fn⟦
  fn io_prop_field_guard(rc: KernelRoles::RoleCtx, is_prop: Field, field_ty: KernelTypes::KExpr,
                         types: Lists::List<KernelTypes::KExpr>) -> () {
      match is_prop {
        0 => {  () } ,
        _ => {
          assert_eq!(KernelLevels::level_equal(ensure_sort_only(rc, field_ty, types), (&(KernelTypes::KLevelNode::Zero))), 1,
            "projection on a Prop structure: field is not a Prop");
          () } ,
      }
    }
⟧

def io_peel_params_subst := aiur_fn⟦
  fn io_peel_params_subst(ty: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>, n_params: Field) -> KernelTypes::KExpr {
      match n_params {
        0 => {  ty } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(_, body, _) => {
              match (*(args)) {
                Lists::Node::Cons(arg, rest) => {
                  let body_substed = KernelSubst::expr_inst1(body, arg, 0);
                  io_peel_params_subst(body_substed, rest, n_params - 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def io_peel_field_loop := aiur_fn⟦
  fn io_peel_field_loop(ty: KernelTypes::KExpr, target: Field, current: Field,
                              struct_addr: Bytes::AddressRef, val: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          match target - current {
            0 => {  dom } ,
            _ => {
              let proj_expr = (&(KernelTypes::KExprNode::Proj(struct_addr, current, val)));
              let body_substed = KernelSubst::expr_inst1(body, proj_expr, 0);
              io_peel_field_loop(body_substed, target, current + 1,
                                      struct_addr, val) } ,
          } } ,
      }
    }
⟧

end

end IxVM
