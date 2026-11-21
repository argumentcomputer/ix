import Aiur.Modules.Function

/-! # Deterministic field-sort classification and explicit zero-signature checks

The classifier has no role context or validation limit. It reads declared types and definition
values, and uses only structural substitution and head delta/beta/let steps. Its output is not
a typing certificate: `checked_sort` also runs ordinary inference and compares zero-signatures.
-/

namespace IxVM

aiur_module KernelGuard where

def level_inst_raw := aiur_fn⟦
  fn level_inst_raw(l: KernelTypes::KLevel, params: Lists::List<KernelTypes::KLevel>) -> KernelTypes::KLevel {
      match (*(l)) {
        KernelTypes::KLevelNode::Zero => {  l } ,
        KernelTypes::KLevelNode::Succ(u) => {  (&(KernelTypes::KLevelNode::Succ(level_inst_raw(u, params)))) } ,
        KernelTypes::KLevelNode::Max(a, b) => {  (&(KernelTypes::KLevelNode::Max(level_inst_raw(a, params), level_inst_raw(b, params)))) } ,
        KernelTypes::KLevelNode::IMax(a, b) => {  (&(KernelTypes::KLevelNode::IMax(level_inst_raw(a, params), level_inst_raw(b, params)))) } ,
        KernelTypes::KLevelNode::Param(i) => {  Lists::lookup(params, i) } ,
      }
    }
⟧

def levels_inst_raw := aiur_fn⟦
  fn levels_inst_raw(ls: Lists::List<KernelTypes::KLevel>, params: Lists::List<KernelTypes::KLevel>) -> Lists::List<KernelTypes::KLevel> {
      match (*(ls)) {
        Lists::Node::Nil => {  ls } ,
        Lists::Node::Cons(l, rest) => {
          (&(Lists::Node::Cons(level_inst_raw(l, params), levels_inst_raw(rest, params)))) } ,
      }
    }
⟧

def expr_inst_raw := aiur_fn⟦
  fn expr_inst_raw(e: KernelTypes::KExpr, params: Lists::List<KernelTypes::KLevel>) -> KernelTypes::KExpr {
      match (*(params)) {
        Lists::Node::Nil => {  e } ,
        _ => {  expr_inst_raw_walk(e, params) } ,
      }
    }
⟧

def expr_inst_raw_walk := aiur_fn⟦
  fn expr_inst_raw_walk(e: KernelTypes::KExpr, params: Lists::List<KernelTypes::KLevel>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(_) => {  e } ,
        KernelTypes::KExprNode::Srt(l) => {  (&(KernelTypes::KExprNode::Srt(level_inst_raw(l, params)))) } ,
        KernelTypes::KExprNode::Const(a, us) => {  (&(KernelTypes::KExprNode::Const(a, levels_inst_raw(us, params)))) } ,
        KernelTypes::KExprNode::App(f, a) => {  (&(KernelTypes::KExprNode::App(expr_inst_raw(f, params), expr_inst_raw(a, params)))) } ,
        KernelTypes::KExprNode::Lam(t, b, m) => {
          (&(KernelTypes::KExprNode::Lam(expr_inst_raw(t, params), expr_inst_raw(b, params), level_inst_raw(m, params)))) } ,
        KernelTypes::KExprNode::Forall(t, b, m) => {
          (&(KernelTypes::KExprNode::Forall(expr_inst_raw(t, params), expr_inst_raw(b, params), level_inst_raw(m, params)))) } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          (&(KernelTypes::KExprNode::Let(expr_inst_raw(t, params), expr_inst_raw(v, params), expr_inst_raw(b, params)))) } ,
        KernelTypes::KExprNode::Lit(_) => {  e } ,
        KernelTypes::KExprNode::Proj(s, i, v) => {  (&(KernelTypes::KExprNode::Proj(s, i, expr_inst_raw(v, params)))) } ,
      }
    }
⟧

def signature_pair := aiur_fn⟦
  fn signature_pair(l: KernelTypes::KLevel) -> (Field, KernelTypes::KLevel) {
      match (*(l)) {
        KernelTypes::KLevelNode::Zero => {  (0, l) } ,
        KernelTypes::KLevelNode::Param(_) => {  (0, l) } ,
        KernelTypes::KLevelNode::Succ(_) => {  (1, (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))))) } ,
        KernelTypes::KLevelNode::IMax(_, b) => {  signature_pair(b) } ,
        KernelTypes::KLevelNode::Max(a, b) => {
          let (na, sa) = signature_pair(a);
          let (nb, sb) = signature_pair(b);
          match na + nb {
            0 => {  (0, (&(KernelTypes::KLevelNode::Max(sa, sb)))) } ,
            _ => {  (1, (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))))) } ,
          } } ,
      }
    }
⟧

def signature_level := aiur_fn⟦
  fn signature_level(l: KernelTypes::KLevel) -> KernelTypes::KLevel {
      let (_, s) = signature_pair(l);
      s
    }
⟧

def declared_type := aiur_fn⟦
  fn declared_type(a: Bytes::AddressRef, us: Lists::List<KernelTypes::KLevel>) -> KernelTypes::KExpr {
      let ci = (*(Ingress::get_ci(a)));
      assert_eq!(Lists::length(us), KernelInfer::const_num_lvls(ci), "field classifier: universe count mismatch");
      expr_inst_raw(KernelInfer::const_type_of(ci), us)
    }
⟧

def definition_value := aiur_fn⟦
  fn definition_value(a: Bytes::AddressRef, us: Lists::List<KernelTypes::KLevel>) -> KernelTypes::KExpr {
      let KernelTypes::KConstantInfo::Defn(nl, _, value, _, _) = (*(Ingress::get_ci(a)));
      assert_eq!(Lists::length(us), nl, "field classifier: definition universe count mismatch");
      expr_inst_raw(value, us)
    }
⟧

def head := aiur_fn⟦
  fn head(e: KernelTypes::KExpr, fuel: Field) -> KernelTypes::KExpr {
      match fuel {
        0 => {  assert_eq!(0, 1, "field classifier: head depth exceeded"); e } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::Srt(_) => {  e } ,
            KernelTypes::KExprNode::Forall(_, _, _) => {  e } ,
            KernelTypes::KExprNode::Lam(_, _, _) => {  e } ,
            KernelTypes::KExprNode::Const(a, us) => {  head(definition_value(a, us), fuel - 1) } ,
            KernelTypes::KExprNode::App(f, a) => {
              let KernelTypes::KExprNode::Lam(_, body, _) = (*(head(f, fuel - 1)));
              head(KernelSubst::expr_inst1(body, a, 0), fuel - 1) } ,
            KernelTypes::KExprNode::Let(_, value, body) => {
              head(KernelSubst::expr_inst1(body, value, 0), fuel - 1) } ,
            _ => {  assert_eq!(0, 1, "field classifier: unsupported type head"); e } ,
          } } ,
      }
    }
⟧

def infer_shape := aiur_fn⟦
  fn infer_shape(e: KernelTypes::KExpr, ctx: Lists::List<KernelTypes::KExpr>, fuel: Field) -> KernelTypes::KExpr {
      match fuel {
        0 => {  assert_eq!(0, 1, "field classifier: inference depth exceeded"); e } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::BVar(i) => {  KernelInfer::types_lookup(ctx, i) } ,
            KernelTypes::KExprNode::Srt(u) => {  (&(KernelTypes::KExprNode::Srt((&(KernelTypes::KLevelNode::Succ(u)))))) } ,
            KernelTypes::KExprNode::Const(a, us) => {  declared_type(a, us) } ,
            KernelTypes::KExprNode::App(f, a) => {
              let tf = infer_shape(f, ctx, fuel - 1);
              let KernelTypes::KExprNode::Forall(_, body, _) = (*(head(tf, fuel - 1)));
              KernelSubst::expr_inst1(body, a, 0) } ,
            KernelTypes::KExprNode::Forall(ty, body, _) => {
              let tb = infer_shape(body, (&(Lists::Node::Cons(ty, ctx))), fuel - 1);
              let KernelTypes::KExprNode::Srt(u) = (*(head(tb, fuel - 1)));
              (&(KernelTypes::KExprNode::Srt(u))) } ,
            KernelTypes::KExprNode::Lam(ty, body, m) => {
              let tb = infer_shape(body, (&(Lists::Node::Cons(ty, ctx))), fuel - 1);
              (&(KernelTypes::KExprNode::Forall(ty, tb, m))) } ,
            KernelTypes::KExprNode::Let(_, value, body) => {
              infer_shape(KernelSubst::expr_inst1(body, value, 0), ctx, fuel - 1) } ,
            _ => {  assert_eq!(0, 1, "field classifier: unsupported field type"); e } ,
          } } ,
      }
    }
⟧

def sort_signature := aiur_fn⟦
  fn sort_signature(e: KernelTypes::KExpr, ctx: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KLevel {
      let t = infer_shape(e, ctx, 10000);
      let KernelTypes::KExprNode::Srt(u) = (*(head(t, 10000)));
      signature_level(u)
    }
⟧

def checked_sort := aiur_fn⟦
  fn checked_sort(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, ctx: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KLevel {
      let actual = KernelInfer::k_ensure_sort(rc, e, ctx);
      let expected = sort_signature(e, ctx);
      assert_eq!(KernelLevels::level_equal(signature_level(actual), expected), 1,
        "field classifier: inferred zero-signature differs");
      actual
    }
⟧

def check_fields := aiur_fn⟦
  fn check_fields(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, np: Field, nf: Field,
                  ctx: Lists::List<KernelTypes::KExpr>) -> () {
      match np {
        0 => {
          match nf {
            0 => {  () } ,
            _ => {
              let KernelTypes::KExprNode::Forall(dom, body, _) = (*(ty));
              checked_sort(rc, dom, ctx);
              check_fields(rc, body, 0, nf - 1, (&(Lists::Node::Cons(dom, ctx)))) } ,
          } } ,
        _ => {
          let KernelTypes::KExprNode::Forall(dom, body, _) = (*(ty));
          check_fields(rc, body, np - 1, nf, (&(Lists::Node::Cons(dom, ctx)))) } ,
      }
    }
⟧

def check_prop_fields := aiur_fn⟦
  fn check_prop_fields(rc: KernelRoles::RoleCtx, ind_level: KernelTypes::KLevel,
                       num_ctors: Field, n_indices: Field, ty: KernelTypes::KExpr, np: Field, nf: Field) -> () {
      match num_ctors {
        1 => {
          match n_indices {
            0 => {
              match KernelLevels::level_equal(ind_level, (&(KernelTypes::KLevelNode::Zero))) {
                1 => {  check_fields(rc, ty, np, nf, (&(Lists::Node::Nil))) } ,
                _ => {
                  assert_eq!(KernelInfer::level_may_be_nonzero(ind_level), 1,
                    "field classifier: unrecognized propositional structure");
                  () } ,
              } } ,
            _ => {  () } ,
          } } ,
        _ => {  () } ,
      }
    }
⟧

def proj_walk_checked := aiur_fn⟦
  fn proj_walk_checked(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, ctx: Lists::List<KernelTypes::KExpr>,
                        k: Field, deps: Lists::List<KernelTypes::KLevel>) -> KernelTypes::KLevel {
      let KernelTypes::KExprNode::Forall(dom, body, _) = (*(ty));
      let s = checked_sort(rc, dom, ctx);
      match k {
        0 => {  KernelInfer::proj_guard_fold(s, deps) } ,
        _ => {
          let deps2 = match KernelSubst::expr_has_bvar_at(body, 0) {
            1 => {  Lists::snoc(deps, s) } ,
            _ => {  deps } ,
          };
          proj_walk_checked(rc, body, (&(Lists::Node::Cons(dom, ctx))), k - 1, deps2) } ,
      }
    }
⟧

end

end IxVM
