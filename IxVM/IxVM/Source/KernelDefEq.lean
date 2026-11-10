import Aiur.Modules.Function

/-! # IxVM module `KernelDefEq`

Definitional equality.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelDefEq where

def level_list_eq := aiur_fn⟦
  fn level_list_eq(a: Lists::List<KernelTypes::KLevel>, b: Lists::List<KernelTypes::KLevel>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          match (*(b)) {
            Lists::Node::Nil => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(x, xs) => {
          match (*(b)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(y, ys) => {
              match KernelLevels::level_equal(x, y) {
                0 => {  0 } ,
                _ => {  level_list_eq(xs, ys) } ,
              } } ,
          } } ,
      }
    }
⟧

def k_is_def_eq := aiur_fn⟦
  fn k_is_def_eq(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let base = KernelSubst::lbr_max(KernelSubst::expr_lbr(a), KernelSubst::expr_lbr(b));
          match base {
            0 => {  k_is_def_eq_core(rc, a, b, (&(Lists::Node::Nil))) } ,
            _ => {  k_def_eq_rebase(rc, a, b, types, base) } ,
          }
    }
⟧

def k_def_eq_rebase := aiur_fn⟦
  fn k_def_eq_rebase(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>,
                           base: Field) -> Field {

      let g = KernelSubst::lbr_min(KernelSubst::lbr_min(KernelSubst::expr_glb(a, 0), KernelSubst::expr_glb(b, 0)),
                      Lists::length(types));
      match g {
        0 => {  k_is_def_eq_core(rc, a, b, KernelSubst::ctx_trim(types, base)) } ,
        _ => {
          k_is_def_eq_core(rc, KernelSubst::expr_lower(a, g, 0), KernelSubst::expr_lower(b, g, 0),
            KernelSubst::ctx_trim(Lists::drop(types, g), base - g)) } ,
      }
    }
⟧


  -- Port divergence: definitional equality runs the ordered tiers, without main's
  -- optional pointer shortcuts (`k_is_def_eq_ordered`).

def k_is_def_eq_core := aiur_fn⟦
  fn k_is_def_eq_core(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      k_is_def_eq_ordered(rc, a, b, types)
    }
⟧

def k_is_def_eq_ordered := aiur_fn⟦
  fn k_is_def_eq_ordered(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {

      match try_def_eq_app(rc, a, b, types) {
        1 => {  1 } ,
        _ => {  k_is_def_eq_slow(rc, a, b, types) } ,
      }
    }
⟧

def try_def_eq_app := aiur_fn⟦
  fn try_def_eq_app(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match KernelTypes::collect_spine(a) {
        (ah, aa) => {
          match KernelTypes::collect_spine(b) {
            (bh, bb) => {
              match (*(ah)) {
                -- Port divergence: spine congruence extends to variable heads, which occur
                -- in the same context-free recursor bodies.
                KernelTypes::KExprNode::BVar(i) => {
                      match (*(bh)) {
                        KernelTypes::KExprNode::BVar(j) => {
                          match i - j {
                            0 => {  de_args(rc, aa, bb, types) } ,
                            _ => {  0 } ,
                          } } ,
                        _ => {  0 } ,
                      } } ,
                    KernelTypes::KExprNode::Const(a_addr, al) => {
                  match (*(bh)) {
                    KernelTypes::KExprNode::Const(b_addr, bl) => {
                      match (1 - Bytes::address_eq(a_addr, b_addr)) {
                        0 => {
                          match level_list_eq(al, bl) {
                            0 => {  0 } ,
                            _ => {
                              match Lists::length(aa) - Lists::length(bb) {
                                0 => {  de_args(rc, aa, bb, types) } ,
                                _ => {  0 } ,
                              } } ,
                          } } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

def de_args := aiur_fn⟦
  fn de_args(rc: KernelRoles::RoleCtx, aa: Lists::List<KernelTypes::KExpr>, bb: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(aa)) {
        Lists::Node::Nil => {
          match (*(bb)) {
            Lists::Node::Nil => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(a, ar) => {
          match (*(bb)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(b, br) => {
              match k_is_def_eq(rc, a, b, types) {
                0 => {  0 } ,
                _ => {  de_args(rc, ar, br, types) } ,
              } } ,
          } } ,
      }
    }
⟧

def is_nat_zero := aiur_fn⟦
  fn is_nat_zero(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::Lit(lit) => {
          match lit {
            KernelTypes::KLiteral::Nat(limbs) => {  KernelKlimbs::klimbs_is_zero(limbs) } ,
            _ => {  0 } ,
          } } ,
        KernelTypes::KExprNode::Const(caddr, _) => {  KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_nat_zero()) } ,
        _ => {  0 } ,
      }
    }
⟧

def nat_offset_of := aiur_fn⟦
  fn nat_offset_of(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr) -> (Field, KernelTypes::KExpr, KernelTypes::KLimbs) {
      match (*(e)) {
        KernelTypes::KExprNode::Lit(lit) => {
          match lit {
            KernelTypes::KLiteral::Nat(n) => {  (1, KernelNatPrim::mk_nat_lit((&(Lists::Node::Nil))), n) } ,
            _ => {  (0, e, (&(Lists::Node::Nil))) } ,
          } } ,
        KernelTypes::KExprNode::App(f, a) => {
          match (*(f)) {
            KernelTypes::KExprNode::Const(caddr, _) => {
              match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_nat_succ()) {
                1 => {
                  match nat_offset_of(rc, a) {
                    (_, base, o) => {  (1, base, KernelKlimbs::klimbs_succ(o)) } ,
                  } } ,
                _ => {  (0, e, (&(Lists::Node::Nil))) } ,
              } } ,
            KernelTypes::KExprNode::App(g, x) => {
              match (*(g)) {
                KernelTypes::KExprNode::Const(caddr, _) => {
                  match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_nat_add()) {
                    1 => {
                      match (*(a)) {
                        KernelTypes::KExprNode::Lit(alit) => {
                          match alit {
                            KernelTypes::KLiteral::Nat(m) => {
                              match nat_offset_of(rc, x) {
                                (1, base, o) => {  (1, base, KernelKlimbs::klimbs_add(o, m)) } ,
                                _ => {  (1, x, m) } ,
                              } } ,
                            _ => {  (0, e, (&(Lists::Node::Nil))) } ,
                          } } ,
                        _ => {  (0, e, (&(Lists::Node::Nil))) } ,
                      } } ,
                    _ => {  (0, e, (&(Lists::Node::Nil))) } ,
                  } } ,
                _ => {  (0, e, (&(Lists::Node::Nil))) } ,
              } } ,
            _ => {  (0, e, (&(Lists::Node::Nil))) } ,
          } } ,
        _ => {  (0, e, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def try_def_eq_nat := aiur_fn⟦
  fn try_def_eq_nat(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> (Field, Field) {
      let za = is_nat_zero(rc, a);
      let zb = is_nat_zero(rc, b);
      match za * zb {
        1 => {  (1, 1) } ,
        _ => {
          match nat_offset_of(rc, a) {
            (ma, ba, oa) => {
              match nat_offset_of(rc, b) {
                (mb, bb, ob) => {
                  match ma * mb {
                    0 => {  (0, 0) } ,
                    _ => {
                      match KernelLevels::klimbs_eq(oa, ob) {
                        0 => {  (0, 0) } ,
                        _ => {  (1, k_is_def_eq(rc, ba, bb, types)) } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def try_string_lit_pair := aiur_fn⟦
  inline fn try_string_lit_pair(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match try_string_lit_one(rc, a, b, types) {
        1 => {  1 } ,
        _ => {  try_string_lit_one(rc, b, a, types) } ,
      }
    }
⟧

def try_string_lit_one := aiur_fn⟦
  fn try_string_lit_one(rc: KernelRoles::RoleCtx, t: KernelTypes::KExpr, s: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(t)) {
        KernelTypes::KExprNode::Lit(lit) => {
          match lit {
            KernelTypes::KLiteral::Str(bs) => {
              k_is_def_eq(rc, KernelNatPrim::str_lit_delta_step(rc, KernelNatPrim::str_lit_to_ctor(rc, bs), types),
                             s, types) } ,
            _ => {  0 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def k_is_def_eq_slow := aiur_fn⟦
  fn k_is_def_eq_slow(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match try_string_lit_pair(rc, a, b, types) {
        1 => {  1 } ,
        _ => {  k_is_def_eq_slow_nd(rc, a, b, types) } ,
      }
    }
⟧

def k_is_def_eq_slow_nd := aiur_fn⟦
  fn k_is_def_eq_slow_nd(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let a_core = KernelWhnf::whnf_struct_core(rc, a, types);
      let b_core = KernelWhnf::whnf_struct_core(rc, b, types);
      match k_is_def_eq_struct_safe(rc, a_core, b_core, types) {
            1 => {  1 } ,
            _ => {
              match try_def_eq_app(rc, a_core, b_core, types) {
                1 => {  1 } ,
                _ => {  k_is_def_eq_slow_nd_after_core(rc, a, b, a_core, b_core, types) } ,
              } } ,
          }
    }
⟧

def k_is_def_eq_slow_nd_after_core := aiur_fn⟦
  fn k_is_def_eq_slow_nd_after_core(rc: KernelRoles::RoleCtx, orig_a: KernelTypes::KExpr, orig_b: KernelTypes::KExpr,
                                           a: KernelTypes::KExpr, b: KernelTypes::KExpr,
                                           types: Lists::List<KernelTypes::KExpr>) -> Field {
      let aw_nd = KernelWhnf::whnf_nd(rc, a, types);
      let bw_nd = KernelWhnf::whnf_nd(rc, b, types);
      match k_is_def_eq_struct_safe(rc, aw_nd, bw_nd, types) {
            1 => {  1 } ,
            _ => {
              match try_def_eq_app(rc, aw_nd, bw_nd, types) {
                1 => {  1 } ,
                _ => {  k_is_def_eq_slow2(rc, orig_a, orig_b, aw_nd, bw_nd, types) } ,
              } } ,
          }
    }
⟧

def k_is_def_eq_struct_safe := aiur_fn⟦
  fn k_is_def_eq_struct_safe(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      -- Port divergence: without the pointer-identity shortcut, equal variables are
      -- decided before the inference tiers. Canonical recursor rules compare open
      -- bodies under an empty context deliberately: their binder types are untrusted.
      match (*(a)) {
            KernelTypes::KExprNode::BVar(i) => {
              match (*(b)) {
                KernelTypes::KExprNode::BVar(j) => {  Fields::is_zero(i - j) } ,
                _ => {  0 } ,
              } } ,
        KernelTypes::KExprNode::Srt(la) => {
          match (*(b)) {
            KernelTypes::KExprNode::Srt(lb) => {  KernelLevels::level_equal(la, lb) } ,
            _ => {  0 } ,
          } } ,
        KernelTypes::KExprNode::Lam(ty_a, body_a) => {
          match (*(b)) {
            KernelTypes::KExprNode::Lam(ty_b, body_b) => {
              match k_is_def_eq(rc, ty_a, ty_b, types) {
                1 => {
                  let inner = (&(Lists::Node::Cons(ty_a, types)));
                  k_is_def_eq(rc, body_a, body_b, inner) } ,
                _ => {  0 } ,
              } } ,
            _ => {  0 } ,
          } } ,
        KernelTypes::KExprNode::Forall(ty_a, body_a) => {
          match (*(b)) {
            KernelTypes::KExprNode::Forall(ty_b, body_b) => {
              match k_is_def_eq(rc, ty_a, ty_b, types) {
                1 => {
                  let inner = (&(Lists::Node::Cons(ty_a, types)));
                  k_is_def_eq(rc, body_a, body_b, inner) } ,
                _ => {  0 } ,
              } } ,
            _ => {  0 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def k_is_def_eq_slow2 := aiur_fn⟦
  fn k_is_def_eq_slow2(rc: KernelRoles::RoleCtx, orig_a: KernelTypes::KExpr, orig_b: KernelTypes::KExpr,
                              aw: KernelTypes::KExpr, bw: KernelTypes::KExpr,
                              types: Lists::List<KernelTypes::KExpr>) -> Field {
      match try_proof_irrel(rc, aw, bw, types) {
            1 => {  1 } ,
            _ => {
              match try_unit_like(rc, aw, bw, types) {
                1 => {  1 } ,
                _ => {
                  match try_eta_struct(rc, aw, bw, types) {
                    1 => {  1 } ,
                    _ => {
                      match try_eta_struct(rc, bw, aw, types) {
                        1 => {  1 } ,
                        _ => {
                          match try_def_eq_nat(rc, aw, bw, types) {
                            (1, eq) => {  eq } ,
                            _ => {
                          match lazy_delta_loop(rc, aw, bw, 16, types) {
                            (1, _, _) => {  1 } ,
                            (_, fa, fb) => {  slow2_after_delta(rc, orig_a, orig_b,
                                                     fa, fb, types) } ,
                          } } ,
                          } } ,
                      } } ,
                  } } ,
              } } ,
          }
    }
⟧

def slow2_after_delta := aiur_fn⟦
  fn slow2_after_delta(rc: KernelRoles::RoleCtx, orig_a: KernelTypes::KExpr, orig_b: KernelTypes::KExpr,
                              fa: KernelTypes::KExpr, fb: KernelTypes::KExpr,
                              types: Lists::List<KernelTypes::KExpr>) -> Field {
      match k_is_def_eq_struct_bounded(rc, fa, fb, 8, types) {
        (1, _) => {  1 } ,
        _ => {  match k_is_def_eq_structure_tree(rc, fa, fb, types) {
          1 => {  1 } ,
          _ => {  slow2_eager_fallback(rc, orig_a, orig_b, types) } ,
        } } ,
      }
    }
⟧

def try_same_proj_head_app := aiur_fn⟦
  fn try_same_proj_head_app(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr,
                                   types: Lists::List<KernelTypes::KExpr>) -> Field {
      let (ah, aa) = KernelTypes::collect_spine(a);
      let (bh, ba) = KernelTypes::collect_spine(b);
      match Lists::length(aa) {
        0 => {  0 } ,
        _ => {  match Lists::length(aa) - Lists::length(ba) {
          0 => {  match (*(ah)) {
            KernelTypes::KExprNode::Proj(sa, ia, ea) => {  match (*(bh)) {
              KernelTypes::KExprNode::Proj(sb, ib, eb) => {
                match Bytes::address_eq(sa, sb) {
                  1 => {  match ia - ib {

                    0 => {  match k_is_def_eq(rc, ea, eb, types) {
                      1 => {  de_args(rc, aa, ba, types) } ,
                      _ => {  0 } ,
                    } } ,
                    _ => {  0 } ,
                  } } ,
                  _ => {  0 } ,
                } } ,
              _ => {  0 } ,
            } } ,
            _ => {  0 } ,
          } } ,
          _ => {  0 } ,
        } } ,
      }
    }
⟧

def k_is_def_eq_structure_tree := aiur_fn⟦
  fn k_is_def_eq_structure_tree(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr,
                                       types: Lists::List<KernelTypes::KExpr>) -> Field {
      match k_is_def_eq_struct_bounded(rc, a, b, 8, types) {
        (1, _) => {  1 } ,
        _ => {  match try_same_proj_head_app(rc, a, b, types) {
          1 => {  1 } ,
          _ => {  k_is_def_eq_structure_tree_app(rc, a, b, types) } ,
        } } ,
      }
    }
⟧

def k_is_def_eq_structure_tree_app := aiur_fn⟦
  fn k_is_def_eq_structure_tree_app(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr,
                                           types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(a)) {
        KernelTypes::KExprNode::App(af, ax) => {  match (*(b)) {
          KernelTypes::KExprNode::App(bf, bx) => {  match k_is_def_eq_structure_tree(rc, af, bf, types) {
            1 => {  k_is_def_eq_structure_tree(rc, ax, bx, types) } ,
            _ => {  0 } ,
          } } ,
          _ => {  0 } ,
        } } ,
        _ => {  0 } ,
      }
    }
⟧

def k_is_def_eq_struct_bounded := aiur_fn⟦
  fn k_is_def_eq_struct_bounded(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, credit: Field,
                                       types: Lists::List<KernelTypes::KExpr>) -> (Field, Field) {
      match (*(a)) {
            KernelTypes::KExprNode::BVar(i) => {
              match (*(b)) {
                KernelTypes::KExprNode::BVar(j) => {
                  match i - j { 0 => {  (1, credit) } , _ => {  (0, credit) } , } } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            KernelTypes::KExprNode::Srt(la) => {
              match (*(b)) {
                KernelTypes::KExprNode::Srt(lb) => {  (KernelLevels::level_equal(la, lb), credit) } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            KernelTypes::KExprNode::Const(addr_a, lvls_a) => {
              match (*(b)) {
                KernelTypes::KExprNode::Const(addr_b, lvls_b) => {
                  match Bytes::address_eq(addr_a, addr_b) {
                    1 => {  (level_list_eq(lvls_a, lvls_b), credit) } ,
                    _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
                  } } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            KernelTypes::KExprNode::App(fa, xa) => {
              match (*(b)) {
                KernelTypes::KExprNode::App(fb, xb) => {
                  match k_is_def_eq_struct_bounded(rc, fa, fb, credit, types) {
                    (1, rest) => {
                      k_is_def_eq_struct_bounded(rc, xa, xb, rest, types) } ,
                    (_, rest) => {  (0, rest) } ,
                  } } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            KernelTypes::KExprNode::Lam(ta, ba) => {
              match (*(b)) {
                KernelTypes::KExprNode::Lam(tb, bb) => {
                  match k_is_def_eq_struct_bounded(rc, ta, tb, credit, types) {
                    (1, rest) => {
                      let types2 = (&(Lists::Node::Cons(ta, types)));
                      k_is_def_eq_struct_bounded(rc, ba, bb, rest, types2) } ,
                    (_, rest) => {  (0, rest) } ,
                  } } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            KernelTypes::KExprNode::Forall(ta, ba) => {
              match (*(b)) {
                KernelTypes::KExprNode::Forall(tb, bb) => {
                  match k_is_def_eq_struct_bounded(rc, ta, tb, credit, types) {
                    (1, rest) => {
                      let types2 = (&(Lists::Node::Cons(ta, types)));
                      k_is_def_eq_struct_bounded(rc, ba, bb, rest, types2) } ,
                    (_, rest) => {  (0, rest) } ,
                  } } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            KernelTypes::KExprNode::Lit(la) => {
              match (*(b)) {
                KernelTypes::KExprNode::Lit(lb) => {  (KernelLevels::literal_eq(la, lb), credit) } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            KernelTypes::KExprNode::Proj(struct_a, fidx_a, ea) => {
              match (*(b)) {
                KernelTypes::KExprNode::Proj(struct_b, fidx_b, eb) => {
                  match Bytes::address_eq(struct_a, struct_b) {
                    1 => {
                      match fidx_a - fidx_b {
                        0 => {  k_is_def_eq_struct_bounded(rc, ea, eb, credit, types) } ,
                        _ => {  (0, credit) } ,
                      } } ,
                    _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
                  } } ,
                _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
              } } ,
            _ => {  k_is_def_eq_struct_spend(rc, a, b, credit, types) } ,
          }
    }
⟧

def k_is_def_eq_struct_spend := aiur_fn⟦
  fn k_is_def_eq_struct_spend(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, credit: Field,
                                     types: Lists::List<KernelTypes::KExpr>) -> (Field, Field) {
      match credit {
        0 => {  (0, 0) } ,
        _ => {
          let rest = credit - 1;
          let aw = KernelWhnf::whnf_nd(rc, a, types);
          let bw = KernelWhnf::whnf_nd(rc, b, types);
          match try_def_eq_nat(rc, aw, bw, types) {
                (1, eq) => {  (eq, rest) } ,
                _ => {
                  match lazy_delta_loop(rc, aw, bw, 8, types) {
                    (1, _, _) => {  (1, rest) } ,
                    (_, fa, fb) => {
                      k_is_def_eq_struct_bounded(rc, fa, fb, rest, types) } ,
                  } } ,
              } } ,
      }
    }
⟧

def slow2_eager_fallback := aiur_fn⟦
  fn slow2_eager_fallback(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let aw = KernelWhnf::whnf(rc, a, types);
      let bw = KernelWhnf::whnf(rc, b, types);
      match try_proof_irrel(rc, aw, bw, types) {
            1 => {  1 } ,
            _ => {
              match try_unit_like(rc, aw, bw, types) {
                1 => {  1 } ,
                _ => {
                  match try_eta_struct(rc, aw, bw, types) {
                    1 => {  1 } ,
                    _ => {
                      match try_eta_struct(rc, bw, aw, types) {
                        1 => {  1 } ,
                        _ => {
                          match try_def_eq_nat(rc, aw, bw, types) {
                            (1, eq) => {  eq } ,
                            _ => {
                              match try_eta_swap(rc, aw, bw, types) {
                                1 => {  1 } ,
                                _ => {  k_is_def_eq_struct(rc, aw, bw, types) } ,
                              } } ,
                          } } ,
                      } } ,
                  } } ,
              } } ,
          }
    }
⟧

def try_eta_struct := aiur_fn⟦
  fn try_eta_struct(rc: KernelRoles::RoleCtx, t: KernelTypes::KExpr, s: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match KernelTypes::collect_spine(s) {
        (s_head, s_args) => {
          match (*(s_head)) {
            KernelTypes::KExprNode::Const(ctor_addr, _) => {
              let ci = (*(Ingress::get_ci(ctor_addr)));
              match ci {
                KernelTypes::KConstantInfo::Ctor(_, _, ind_block_addr, ind_idx, _, nparams, nfields, _) => {
                  match Lists::length(s_args) - (nparams + nfields) {
                    0 => {
                      let ind_ci = (*(Ingress::get_ci_iprj(ind_block_addr, ind_idx)));
                      match ind_ci {
                        KernelTypes::KConstantInfo::Induct(_, _, _, nindices, nctors, _, _, _) => {
                          let shape_ok = Fields::is_zero(nindices) * Fields::is_zero(nctors - 1);
                          match shape_ok {
                            0 => {  0 } ,
                            _ => {
                              let struct_addr = compute_iprj_addr(ind_block_addr, ind_idx);

                              match KernelWhnf::struct_is_rec(struct_addr) {
                                1 => {  0 } ,
                                _ => {

                                  let t_ty = KernelInferOnly::k_infer_only(rc, t, types);
                                  let s_ty = KernelInferOnly::k_infer_only(rc, s, types);
                                  match k_is_def_eq(rc, t_ty, s_ty, types) {
                                    0 => {  0 } ,
                                    _ => {
                                      compare_struct_fields(rc, struct_addr, nparams,
                                                                 nfields, t, s_args, 0, types) } ,
                                  } } ,
                              } } ,
                          } } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def compare_struct_fields := aiur_fn⟦
  fn compare_struct_fields(rc: KernelRoles::RoleCtx, struct_addr: Bytes::AddressRef, nparams: Field, nfields: Field,
                                  t: KernelTypes::KExpr, s_args: Lists::List<KernelTypes::KExpr>, i: Field,
                                  types: Lists::List<KernelTypes::KExpr>) -> Field {
      match nfields - i {
        0 => {  1 } ,
        _ => {
          let proj_expr = (&(KernelTypes::KExprNode::Proj(struct_addr, i, t)));
          let s_field = Lists::lookup(s_args, nparams + i);
          match k_is_def_eq(rc, proj_expr, s_field, types) {
            0 => {  0 } ,
            _ => {  compare_struct_fields(rc, struct_addr, nparams, nfields, t,
                                            s_args, i + 1, types) } ,
          } } ,
      }
    }
⟧

def compute_iprj_addr := aiur_fn⟦
  fn compute_iprj_addr(block_addr: Bytes::AddressRef, idx: Field) -> Bytes::AddressRef {

      let idx_u64 = UInt64::from_field(idx);
      let info = Ixon::ConstantInfo::IPrj(Ixon::InductiveProj::Mk(idx_u64, block_addr));
      let proj_c = Ixon::Constant::Mk(info,
                                (&(Lists::Node::Nil)),
                                (&(Lists::Node::Nil)),
                                (&(Lists::Node::Nil)));
      let bytes = IxonSerialize::put_constant(proj_c, (&(Lists::Node::Nil)));
      Blake3::bytes_to_addr(bytes)
    }
⟧

def try_eta_swap := aiur_fn⟦
  fn try_eta_swap(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(a)) {
        KernelTypes::KExprNode::Lam(ta, ba) => {
          match (*(b)) {
            KernelTypes::KExprNode::Lam(_, _) => {  0 } ,
            _ => {  try_eta_expand(rc, ta, ba, b, types) } ,
          } } ,
        _ => {
          match (*(b)) {
            KernelTypes::KExprNode::Lam(tb, bb) => {  try_eta_expand(rc, tb, bb, a, types) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def try_unit_like := aiur_fn⟦
  fn try_unit_like(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let ta = KernelInferOnly::k_infer_only(rc, a, types);
      let ta_w = KernelWhnf::whnf(rc, ta, types);
      match is_unit_like_type(ta_w) {
        0 => {  0 } ,
        _ => {
          let tb = KernelInferOnly::k_infer_only(rc, b, types);
          k_is_def_eq(rc, ta, tb, types) } ,
      }
    }
⟧

def is_unit_like_type := aiur_fn⟦
  fn is_unit_like_type(ty: KernelTypes::KExpr) -> Field {
      match KernelTypes::collect_spine(ty) {
        (head, _) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(addr, _) => {
              let ci = (*(Ingress::get_ci(addr)));
              match ci {
                KernelTypes::KConstantInfo::Induct(_, _, _, n_indices, num_ctors, _, block, idx) => {

                  match n_indices {
                    0 => {
                      match num_ctors - 1 {
                        0 => {
                          let cci = (*(Ingress::get_ci_cprj(block, idx, 0)));
                          match cci {
                            KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, _, nfields, _) => {
                              match nfields {
                                0 => {  1 } ,
                                _ => {  0 } ,
                              } } ,
                            _ => {  0 } ,
                          } } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def try_proof_irrel := aiur_fn⟦
  fn try_proof_irrel(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let a_ty = KernelInferOnly::k_infer_only(rc, a, types);
      match is_prop_type(rc, a_ty, types) {
        0 => {  0 } ,
        _ => {
          let b_ty = KernelInferOnly::k_infer_only(rc, b, types);
          k_is_def_eq(rc, a_ty, b_ty, types) } ,
      }
    }
⟧

def try_eta_expand := aiur_fn⟦
  fn try_eta_expand(rc: KernelRoles::RoleCtx, ty_a: KernelTypes::KExpr, body_a: KernelTypes::KExpr, b: KernelTypes::KExpr,
                          types: Lists::List<KernelTypes::KExpr>) -> Field {
      let b_ty = KernelInferOnly::k_infer_only(rc, b, types);
      let b_ty_w = KernelWhnf::whnf(rc, b_ty, types);
      match (*(b_ty_w)) {
        KernelTypes::KExprNode::Forall(dom_b, _) => {
          match k_is_def_eq(rc, ty_a, dom_b, types) {
            0 => {  0 } ,
            _ => {
              let b_lifted = KernelSubst::expr_lift(b, 1, 0);
              let bvar0 = (&(KernelTypes::KExprNode::BVar(0)));
              let b_app = (&(KernelTypes::KExprNode::App(b_lifted, bvar0)));
              let inner = (&(Lists::Node::Cons(ty_a, types)));
              k_is_def_eq(rc, body_a, b_app, inner) } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def is_prop_type := aiur_fn⟦
  fn is_prop_type(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let sort = KernelInferOnly::k_infer_only(rc, ty, types);
      let sort_w = KernelWhnf::whnf(rc, sort, types);
      match (*(sort_w)) {
        KernelTypes::KExprNode::Srt(l) => {  KernelLevels::level_equal(l, (&(KernelTypes::KLevelNode::Zero))) } ,
        _ => {  0 } ,
      }
    }
⟧

def k_is_def_eq_struct := aiur_fn⟦
  fn k_is_def_eq_struct(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      k_is_def_eq_struct_go(rc, a, b, types)
    }
⟧

def k_is_def_eq_struct_go := aiur_fn⟦
  fn k_is_def_eq_struct_go(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(a)) {
        KernelTypes::KExprNode::BVar(i) => {
          match (*(b)) {
            KernelTypes::KExprNode::BVar(j) => {  match i - j { 0 => {  1 } , _ => {  0 } , } } ,
            _ => {  0 } ,
          } } ,
        KernelTypes::KExprNode::Srt(la) => {
          match (*(b)) {
            KernelTypes::KExprNode::Srt(lb) => {  KernelLevels::level_equal(la, lb) } ,
            _ => {  0 } ,
          } } ,
        KernelTypes::KExprNode::Const(addr_a, lvls_a) => {
          match (*(b)) {
            KernelTypes::KExprNode::Const(addr_b, lvls_b) => {

              match Bytes::address_eq(addr_a, addr_b) {
                1 => {  level_list_eq(lvls_a, lvls_b) } ,
                _ => {  try_lazy_delta_app(rc, a, b, types) } ,
              } } ,
            _ => {  try_lazy_delta_app(rc, a, b, types) } ,
          } } ,
        KernelTypes::KExprNode::App(fa, xa) => {
          match (*(b)) {
            KernelTypes::KExprNode::App(fb, xb) => {
              match k_is_def_eq(rc, fa, fb, types) {
                0 => {  try_lazy_delta_app(rc, a, b, types) } ,
                _ => {
                  match k_is_def_eq(rc, xa, xb, types) {
                    0 => {  try_lazy_delta_app(rc, a, b, types) } ,
                    _ => {  1 } ,
                  } } ,
              } } ,
            _ => {  try_lazy_delta_app(rc, a, b, types) } ,
          } } ,
        KernelTypes::KExprNode::Lam(ta, ba) => {
          match (*(b)) {
            KernelTypes::KExprNode::Lam(tb, bb) => {
              match k_is_def_eq(rc, ta, tb, types) {
                0 => {  0 } ,
                _ => {
                  let types2 = (&(Lists::Node::Cons(ta, types)));
                  k_is_def_eq(rc, ba, bb, types2) } ,
              } } ,
            _ => {  try_eta_expand(rc, ta, ba, b, types) } ,
          } } ,
        KernelTypes::KExprNode::Forall(ta, ba) => {
          match (*(b)) {
            KernelTypes::KExprNode::Forall(tb, bb) => {
              match k_is_def_eq(rc, ta, tb, types) {
                0 => {  0 } ,
                _ => {
                  let types2 = (&(Lists::Node::Cons(ta, types)));
                  k_is_def_eq(rc, ba, bb, types2) } ,
              } } ,
            _ => {  0 } ,
          } } ,
        KernelTypes::KExprNode::Let(_, _, _) => {

          0 } ,
        KernelTypes::KExprNode::Lit(la) => {
          match (*(b)) {

            KernelTypes::KExprNode::Lit(lb) => {  KernelLevels::literal_eq(la, lb) } ,
            _ => {

                  -- Port divergence: a progress guard, not an equality shortcut. Nat literals
                  -- expand to Const/App and String literals stay, so the literal tag decides.
              match la {
                    KernelTypes::KLiteral::Nat(_) => {
                      k_is_def_eq_struct_go(rc, KernelWhnf::nat_lit_to_ctor_or_self(rc, a), b, types) } ,
                    KernelTypes::KLiteral::Str(_) => {  0 } ,
                  } } ,
          } } ,
        KernelTypes::KExprNode::Proj(struct_a, fidx_a, ea) => {
          match (*(b)) {
            KernelTypes::KExprNode::Proj(struct_b, fidx_b, eb) => {

              match Bytes::address_eq(struct_a, struct_b) {
                1 => {
                  match fidx_a - fidx_b {
                    0 => {  k_is_def_eq(rc, ea, eb, types) } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def lazy_delta_loop := aiur_fn⟦
  fn lazy_delta_loop(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, fuel: Field,
                            types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      match fuel {
        0 => {  (0, a, b) } ,
        _ => {
          match try_def_eq_nat(rc, a, b, types) {
            (1, eq) => {  (eq, a, b) } ,
            _ => {
          let (a_addr, a_is_const) = head_addr(a);
          let (b_addr, b_is_const) = head_addr(b);
          match a_is_const {
            1 => {
              match b_is_const {
                1 => {

                  lazy_delta_step_const_const(rc, a_addr, b_addr, a, b,
                                               fuel, types) } ,
                _ => {  lazy_delta_a_const_b_proj(rc, a_addr, a, b, fuel, types) } ,
              } } ,
            _ => {
              match b_is_const {
                1 => {  lazy_delta_b_const_a_proj(rc, b_addr, a, b, fuel, types) } ,
                _ => {

                  lazy_delta_both_proj(rc, a, b, fuel, types) } ,
              } } ,
          } } ,
          } } ,
      }
    }
⟧

def delta_rank := aiur_fn⟦
  fn delta_rank(ci: KernelTypes::KConstantInfo) -> Field {
      match ci {
        KernelTypes::KConstantInfo::Defn(_, _, _, _, hint) => {  hint } ,
        _ => {  0 } ,
      }
    }
⟧

def lazy_delta_step_const_const := aiur_fn⟦
  fn lazy_delta_step_const_const(rc: KernelRoles::RoleCtx, a_addr: Bytes::AddressRef, b_addr: Bytes::AddressRef, a: KernelTypes::KExpr,
                                         b: KernelTypes::KExpr, fuel: Field,
                                         types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      let a_ci = (*(Ingress::get_ci(a_addr)));
      let b_ci = (*(Ingress::get_ci(b_addr)));
      let ae = is_defn_or_thm(a_ci);
      let be = is_defn_or_thm(b_ci);
      match ae {
        0 => {
          match be {
            0 => {  (0, a, b) } ,
            _ => {  unfold_b_and_loop(rc, a, b, fuel, types) } ,
          } } ,
        _ => {
          match be {
            0 => {  unfold_a_and_loop(rc, a, b, fuel, types) } ,
            _ => {
              let ar = delta_rank(a_ci);
              let br = delta_rank(b_ci);
              match UInt32::less_than_fields(br, ar) {
                1 => {  unfold_a_and_loop(rc, a, b, fuel, types) } ,
                _ => {
                  match UInt32::less_than_fields(ar, br) {
                    1 => {  unfold_b_and_loop(rc, a, b, fuel, types) } ,
                    _ => {  unfold_both_and_loop(rc, a, b, fuel, types) } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def unfold_a_and_loop := aiur_fn⟦
  fn unfold_a_and_loop(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, fuel: Field,
                             types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      match delta_unfold(a) {
        (1, a2) => {
          let aw = KernelWhnf::whnf_nd(rc, a2, types);
          lazy_delta_loop(rc, aw, b, fuel - 1, types) } ,
        _ => {  (0, a, b) } ,
      }
    }
⟧

def unfold_b_and_loop := aiur_fn⟦
  fn unfold_b_and_loop(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, fuel: Field,
                             types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      match delta_unfold(b) {
        (1, b2) => {
          let bw = KernelWhnf::whnf_nd(rc, b2, types);
          lazy_delta_loop(rc, a, bw, fuel - 1, types) } ,
        _ => {  (0, a, b) } ,
      }
    }
⟧

def unfold_both_and_loop := aiur_fn⟦
  fn unfold_both_and_loop(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, fuel: Field,
                                types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      match delta_unfold(a) {
        (1, a2) => {
          match delta_unfold(b) {
            (1, b2) => {
              let aw = KernelWhnf::whnf_nd(rc, a2, types);
              let bw = KernelWhnf::whnf_nd(rc, b2, types);
              lazy_delta_loop(rc, aw, bw, fuel - 1, types) } ,
            _ => {  (0, a, b) } ,
          } } ,
        _ => {  (0, a, b) } ,
      }
    }
⟧

def lazy_delta_a_const_b_proj := aiur_fn⟦
  fn lazy_delta_a_const_b_proj(rc: KernelRoles::RoleCtx, a_addr: Bytes::AddressRef, a: KernelTypes::KExpr, b: KernelTypes::KExpr, fuel: Field,
                                         types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {

      match try_unfold_proj_app(rc, b, types) {
        (1, b2) => {
          lazy_delta_loop(rc, a, b2, fuel - 1, types) } ,
        _ => {
          let a_ci = (*(Ingress::get_ci(a_addr)));
          match is_defn_or_thm(a_ci) {
            0 => {  (0, a, b) } ,
            _ => {
              let au = try_unfold_head(rc, a, a_ci, types);
              match au {
                (1, aw) => {
                  lazy_delta_loop(rc, aw, b, fuel - 1, types) } ,
                _ => {  (0, a, b) } ,
              } } ,
          } } ,
      }
    }
⟧

def lazy_delta_b_const_a_proj := aiur_fn⟦
  fn lazy_delta_b_const_a_proj(rc: KernelRoles::RoleCtx, b_addr: Bytes::AddressRef, a: KernelTypes::KExpr, b: KernelTypes::KExpr, fuel: Field,
                                         types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      match try_unfold_proj_app(rc, a, types) {
        (1, a2) => {
          lazy_delta_loop(rc, a2, b, fuel - 1, types) } ,
        _ => {
          let b_ci = (*(Ingress::get_ci(b_addr)));
          match is_defn_or_thm(b_ci) {
            0 => {  (0, a, b) } ,
            _ => {
              let bu = try_unfold_head(rc, b, b_ci, types);
              match bu {
                (1, bw) => {
                  lazy_delta_loop(rc, a, bw, fuel - 1, types) } ,
                _ => {  (0, a, b) } ,
              } } ,
          } } ,
      }
    }
⟧

def lazy_delta_both_proj := aiur_fn⟦
  fn lazy_delta_both_proj(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, fuel: Field,
                                 types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      let ua = try_unfold_proj_app(rc, a, types);
      let ub = try_unfold_proj_app(rc, b, types);
      match ua {
        (1, a2) => {
          match ub {
            (1, b2) => {
              lazy_delta_loop(rc, a2, b2, fuel - 1, types) } ,
            _ => {
              lazy_delta_loop(rc, a2, b, fuel - 1, types) } ,
          } } ,
        _ => {
          match ub {
            (1, b2) => {
              lazy_delta_loop(rc, a, b2, fuel - 1, types) } ,
            _ => {  (0, a, b) } ,
          } } ,
      }
    }
⟧

def is_defn_or_thm := aiur_fn⟦
  fn is_defn_or_thm(ci: KernelTypes::KConstantInfo) -> Field {
      match ci {
        KernelTypes::KConstantInfo::Defn(_, _, _, _, _) => {  1 } ,
        KernelTypes::KConstantInfo::Thm(_, _, _) => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def try_unfold_proj_app := aiur_fn⟦
  fn try_unfold_proj_app(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match KernelTypes::collect_spine(e) {
        (head, spine) => {
          match (*(head)) {
            KernelTypes::KExprNode::Proj(struct_addr, fidx, inner) => {
              let reduced = KernelWhnf::whnf_nd(rc, e, types);
              match KernelTypes::collect_spine(reduced) {
                (reduced_head, _) => {
                  match (*(reduced_head)) {
                    KernelTypes::KExprNode::Proj(_, _, _) => {
                      match delta_unfold(inner) {
                        (1, inner2) => {
                          let new_head = (&(KernelTypes::KExprNode::Proj(struct_addr, fidx, inner2)));
                          (1, KernelWhnf::apply_spine(new_head, spine)) } ,
                        _ => {  (0, e) } ,
                      } } ,
                    _ => {  (1, reduced) } ,
                  } } ,
              } } ,
            _ => {  (0, e) } ,
          } } ,
      }
    }
⟧

def delta_unfold := aiur_fn⟦
  fn delta_unfold(e: KernelTypes::KExpr) -> (Field, KernelTypes::KExpr) {
      match KernelTypes::collect_spine(e) {
        (head, spine) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(addr, lvls) => {
              let ci = (*(Ingress::get_ci(addr)));
              match ci {
                KernelTypes::KConstantInfo::Defn(_, _, value, _, _) => {
                  let body = KernelLevels::expr_inst_levels(value, lvls);
                  (1, KernelWhnf::apply_spine(body, spine)) } ,
                KernelTypes::KConstantInfo::Thm(_, _, value) => {
                  let body = KernelLevels::expr_inst_levels(value, lvls);
                  (1, KernelWhnf::apply_spine(body, spine)) } ,
                _ => {  (0, e) } ,
              } } ,
            _ => {  (0, e) } ,
          } } ,
      }
    }
⟧

def try_lazy_delta_app := aiur_fn⟦
  fn try_lazy_delta_app(rc: KernelRoles::RoleCtx, a: KernelTypes::KExpr, b: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let (a_addr, a_is_const) = head_addr(a);
      let (b_addr, b_is_const) = head_addr(b);
      match a_is_const {
        0 => {  0 } ,
        _ => {
          match b_is_const {
            0 => {  0 } ,
            _ => {
              let a_ci = (*(Ingress::get_ci(a_addr)));
              let b_ci = (*(Ingress::get_ci(b_addr)));
              let a_unfolded = try_unfold_head(rc, a, a_ci, types);
              let b_unfolded = try_unfold_head(rc, b, b_ci, types);
              match a_unfolded {
                (1, aw) => {
                  match b_unfolded {
                    (1, bw) => {  k_is_def_eq(rc, aw, bw, types) } ,
                    _ => {  k_is_def_eq(rc, aw, b, types) } ,
                  } } ,
                (0, _) => {
                  match b_unfolded {
                    (1, bw) => {  k_is_def_eq(rc, a, bw, types) } ,
                    _ => {  0 } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def head_addr := aiur_fn⟦
  fn head_addr(e: KernelTypes::KExpr) -> (Bytes::AddressRef, Field) {
      match KernelTypes::collect_spine(e) {
        (head, _) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(addr, _) => {  (addr, 1) } ,
            _ => {  ((&([UInt8::BYTE_0; 32])), 0) } ,
          } } ,
      }
    }
⟧

def try_unfold_head := aiur_fn⟦
  fn try_unfold_head(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, ci: KernelTypes::KConstantInfo,
                           types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match ci {

        KernelTypes::KConstantInfo::Defn(_, _, _, _, _) => {
          match delta_unfold(e) {
            (1, e2) => {  (1, KernelWhnf::whnf_nd(rc, e2, types)) } ,
            _ => {  (0, e) } ,
          } } ,
        KernelTypes::KConstantInfo::Thm(_, _, _) => {
          match delta_unfold(e) {
            (1, e2) => {  (1, KernelWhnf::whnf_nd(rc, e2, types)) } ,
            _ => {  (0, e) } ,
          } } ,
        _ => {  (0, e) } ,
      }
    }
⟧

end

end IxVM
