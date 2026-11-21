import Aiur.Modules.Function

/-! # IxVM module `KernelSubst`

Substitution, loose bound variables and context cuts.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelSubst where

def expr_lbr := aiur_fn⟦
  fn expr_lbr(e: KernelTypes::KExpr) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(i) => {  i + 1 } ,
        KernelTypes::KExprNode::Srt(_) => {  0 } ,
        KernelTypes::KExprNode::Const(_, _) => {  0 } ,
        KernelTypes::KExprNode::Lit(_) => {  0 } ,
        KernelTypes::KExprNode::App(f, a) => {  lbr_max(expr_lbr(f), expr_lbr(a)) } ,
        KernelTypes::KExprNode::Lam(ty, body, _) => {
          lbr_max(expr_lbr(ty), lbr_dec(expr_lbr(body))) } ,
        KernelTypes::KExprNode::Forall(ty, body, _) => {
          lbr_max(expr_lbr(ty), lbr_dec(expr_lbr(body))) } ,
        KernelTypes::KExprNode::Let(ty, val, body) => {  expr_lbr_let(ty, val, body) } ,
        KernelTypes::KExprNode::Proj(_, _, e1) => {  expr_lbr(e1) } ,
      }
    }
⟧

def expr_lbr_let := aiur_fn⟦
  fn expr_lbr_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr) -> Field {
      lbr_max(lbr_max(expr_lbr(ty), expr_lbr(val)),
              lbr_dec(expr_lbr(body)))
    }
⟧

def lbr_max := aiur_fn⟦
  fn lbr_max(a: Field, b: Field) -> Field {
      match UInt32::less_than_fields(a, b) {
        1 => {  b } ,
        0 => {  a } ,
      }
    }
⟧

def lbr_dec := aiur_fn⟦
  fn lbr_dec(n: Field) -> Field {
      match n {
        0 => {  0 } ,
        _ => {  n - 1 } ,
      }
    }
⟧

def lbr_min := aiur_fn⟦
  fn lbr_min(a: Field, b: Field) -> Field {
      match UInt32::less_than_fields(a, b) {
        1 => {  a } ,
        0 => {  b } ,
      }
    }
⟧

def has_bvar_in_range := aiur_fn⟦
  fn has_bvar_in_range(e: KernelTypes::KExpr, lo: Field, hi: Field) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(i) => {  has_bvar_in_range_bvar(i, lo, hi) } ,
        KernelTypes::KExprNode::Srt(_) => {  0 } ,
        KernelTypes::KExprNode::Const(_, _) => {  0 } ,
        KernelTypes::KExprNode::Lit(_) => {  0 } ,
        KernelTypes::KExprNode::App(f, a) => {
          match has_bvar_in_range(f, lo, hi) {
            1 => {  1 } ,
            0 => {  has_bvar_in_range(a, lo, hi) } ,
          } } ,
        KernelTypes::KExprNode::Lam(ty, body, _) => {  has_bvar_in_range_binder(ty, body, lo, hi) } ,
        KernelTypes::KExprNode::Forall(ty, body, _) => {  has_bvar_in_range_binder(ty, body, lo, hi) } ,
        KernelTypes::KExprNode::Let(ty, val, body) => {  has_bvar_in_range_let(ty, val, body, lo, hi) } ,
        KernelTypes::KExprNode::Proj(_, _, e1) => {  has_bvar_in_range(e1, lo, hi) } ,
      }
    }
⟧

def has_bvar_in_range_bvar := aiur_fn⟦
  fn has_bvar_in_range_bvar(i: Field, lo: Field, hi: Field) -> Field {
      match UInt32::less_than_fields(i, lo) {
        1 => {  0 } ,
        0 => {  UInt32::less_than_fields(i, hi) } ,
      }
    }
⟧

def has_bvar_in_range_binder := aiur_fn⟦
  fn has_bvar_in_range_binder(ty: KernelTypes::KExpr, body: KernelTypes::KExpr, lo: Field, hi: Field) -> Field {
      match has_bvar_in_range(ty, lo, hi) {
        1 => {  1 } ,
        0 => {  has_bvar_in_range(body, lo + 1, hi + 1) } ,
      }
    }
⟧

def has_bvar_in_range_let := aiur_fn⟦
  fn has_bvar_in_range_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr, lo: Field, hi: Field) -> Field {
      match has_bvar_in_range(ty, lo, hi) {
        1 => {  1 } ,
        0 => {
          match has_bvar_in_range(val, lo, hi) {
            1 => {  1 } ,
            0 => {  has_bvar_in_range(body, lo + 1, hi + 1) } ,
          } } ,
      }
    }
⟧

def ctx_reachable := aiur_fn⟦
  inline fn ctx_reachable(types: Lists::List<KernelTypes::KExpr>, base: Field) -> Field {
      let len = Lists::length(types);
      ctx_seek_cut(types, lbr_min(base, len))
    }
⟧

def ctx_seek_cut := aiur_fn⟦
  fn ctx_seek_cut(types: Lists::List<KernelTypes::KExpr>, need: Field) -> Field {
      let c = ctx_next_cut(types);
      match UInt32::less_than_fields(c, need) {
        0 => {  c } ,
        1 => {  c + ctx_seek_cut(Lists::drop(types, c), need - c) } ,
      }
    }
⟧

def ctx_next_cut := aiur_fn⟦
  fn ctx_next_cut(types: Lists::List<KernelTypes::KExpr>) -> Field {
      let Lists::Node::Cons(ty, rest) = (*(types));
      1 + ctx_close_cut(rest, expr_lbr(ty))
    }
⟧


  -- Port divergence: canonical recursor rules compare open bodies under an empty
  -- context. Entering a higher-order induction hypothesis (e.g. Acc.rec) pushes open
  -- binder types whose loose range reaches past the partial context, so a cut that
  -- runs out of context closes at 0 instead of recursing into Nil.

def ctx_close_cut := aiur_fn⟦
  fn ctx_close_cut(rest: Lists::List<KernelTypes::KExpr>, l: Field) -> Field {
      match l {
        0 => {  0 } ,
        _ => {
          match (*(rest)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(_, _) => {
              let c = ctx_next_cut(rest);
              match UInt32::less_than_fields(c, l) {
                0 => {  c } ,
                1 => {  c + ctx_close_cut(Lists::drop(rest, c), l - c) } ,
              } } ,
          } } ,
      }
    }
⟧

def ctx_trim := aiur_fn⟦
  fn ctx_trim(types: Lists::List<KernelTypes::KExpr>, base: Field) -> Lists::List<KernelTypes::KExpr> {
      match base {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          match UInt32::less_than_fields(base, Lists::length(types)) {
            0 => {  types } ,
            1 => {  Lists::take(types, ctx_reachable(types, base)) } ,
          } } ,
      }
    }
⟧

def expr_glb := aiur_fn⟦
  fn expr_glb(e: KernelTypes::KExpr, c: Field) -> Field {

      match UInt32::less_than_fields(expr_lbr(e), c + 1) {
        1 => {  4294967295 } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::BVar(i) => {  i - c } ,
            KernelTypes::KExprNode::App(f, a) => {  match expr_glb(f, c) {
              0 => {  0 } ,
              n => {  lbr_min(n, expr_glb(a, c)) } ,
            } } ,
            KernelTypes::KExprNode::Lam(ty, body, _) => {  match expr_glb(ty, c) {
              0 => {  0 } ,
              n => {  lbr_min(n, expr_glb(body, c + 1)) } ,
            } } ,
            KernelTypes::KExprNode::Forall(ty, body, _) => {  match expr_glb(ty, c) {
              0 => {  0 } ,
              n => {  lbr_min(n, expr_glb(body, c + 1)) } ,
            } } ,
            KernelTypes::KExprNode::Let(ty, val, body) => {  expr_glb_let(ty, val, body, c) } ,
            KernelTypes::KExprNode::Proj(_, _, e1) => {  expr_glb(e1, c) } ,
            _ => {  4294967295 } ,
          } } ,
      }
    }
⟧

def expr_glb_let := aiur_fn⟦
  fn expr_glb_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr, c: Field) -> Field {
      match expr_glb(ty, c) {
        0 => {  0 } ,
        n => {  match expr_glb(val, c) {
          0 => {  0 } ,
          m => {  lbr_min(lbr_min(n, m), expr_glb(body, c + 1)) } ,
        } } ,
      }
    }
⟧

def expr_lift := aiur_fn⟦
  fn expr_lift(e: KernelTypes::KExpr, shift: Field, cutoff: Field) -> KernelTypes::KExpr {
      match shift {
        0 => {  e } ,
        _ => {
          let l = expr_lbr(e);
          match UInt32::less_than_fields(cutoff, l) {
            0 => {  e } ,
            1 => {
              match (*(e)) {
                KernelTypes::KExprNode::BVar(i) => {  (&(KernelTypes::KExprNode::BVar(i + shift))) } ,
                KernelTypes::KExprNode::App(f, a) => {
                  (&(KernelTypes::KExprNode::App(
                    expr_lift(f, shift, cutoff),
                    expr_lift(a, shift, cutoff)))) } ,
                KernelTypes::KExprNode::Lam(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Lam(
                    expr_lift(ty, shift, cutoff),
                    expr_lift(body, shift, cutoff + 1), bl))) } ,
                KernelTypes::KExprNode::Forall(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Forall(
                    expr_lift(ty, shift, cutoff),
                    expr_lift(body, shift, cutoff + 1), bl))) } ,
                KernelTypes::KExprNode::Let(ty, val, body) => {  expr_lift_let(ty, val, body, shift, cutoff) } ,
                KernelTypes::KExprNode::Proj(tidx, fidx, e1) => {
                  (&(KernelTypes::KExprNode::Proj(tidx, fidx, expr_lift(e1, shift, cutoff)))) } ,
                _ => {  e } ,
              } } ,
          } } ,
      }
    }
⟧

def expr_lift_let := aiur_fn⟦
  fn expr_lift_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr, shift: Field, cutoff: Field)
        -> KernelTypes::KExpr {
      (&(KernelTypes::KExprNode::Let(
        expr_lift(ty, shift, cutoff),
        expr_lift(val, shift, cutoff),
        expr_lift(body, shift, cutoff + 1))))
    }
⟧

def expr_lower := aiur_fn⟦
  fn expr_lower(e: KernelTypes::KExpr, shift: Field, cutoff: Field) -> KernelTypes::KExpr {
      match shift {
        0 => {  e } ,
        _ => {
          let l = expr_lbr(e);
          match UInt32::less_than_fields(cutoff, l) {
            0 => {  e } ,
            1 => {
              match (*(e)) {
                KernelTypes::KExprNode::BVar(i) => {  (&(KernelTypes::KExprNode::BVar(i - shift))) } ,
                KernelTypes::KExprNode::App(f, a) => {
                  (&(KernelTypes::KExprNode::App(
                    expr_lower(f, shift, cutoff),
                    expr_lower(a, shift, cutoff)))) } ,
                KernelTypes::KExprNode::Lam(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Lam(
                    expr_lower(ty, shift, cutoff),
                    expr_lower(body, shift, cutoff + 1), bl))) } ,
                KernelTypes::KExprNode::Forall(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Forall(
                    expr_lower(ty, shift, cutoff),
                    expr_lower(body, shift, cutoff + 1), bl))) } ,
                KernelTypes::KExprNode::Let(ty, val, body) => {  expr_lower_let(ty, val, body, shift, cutoff) } ,
                KernelTypes::KExprNode::Proj(tidx, fidx, e1) => {
                  (&(KernelTypes::KExprNode::Proj(tidx, fidx, expr_lower(e1, shift, cutoff)))) } ,
                _ => {  e } ,
              } } ,
          } } ,
      }
    }
⟧

def expr_lower_let := aiur_fn⟦
  fn expr_lower_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr, shift: Field, cutoff: Field) -> KernelTypes::KExpr {
      (&(KernelTypes::KExprNode::Let(
        expr_lower(ty, shift, cutoff),
        expr_lower(val, shift, cutoff),
        expr_lower(body, shift, cutoff + 1))))
    }
⟧

def expr_has_bvar_at := aiur_fn⟦
  fn expr_has_bvar_at(e: KernelTypes::KExpr, depth: Field) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(i) => {  match i - depth { 0 => {  1 } , _ => {  0 } , } } ,
        KernelTypes::KExprNode::App(f, a) => {
          match expr_has_bvar_at(f, depth) {
            1 => {  1 } ,
            _ => {  expr_has_bvar_at(a, depth) } ,
          } } ,
        KernelTypes::KExprNode::Lam(ty, body, _) => {  expr_has_bvar_at_binder(ty, body, depth) } ,
        KernelTypes::KExprNode::Forall(ty, body, _) => {  expr_has_bvar_at_binder(ty, body, depth) } ,
        KernelTypes::KExprNode::Let(ty, val, body) => {  expr_has_bvar_at_let(ty, val, body, depth) } ,
        KernelTypes::KExprNode::Proj(_, _, inner) => {  expr_has_bvar_at(inner, depth) } ,
        _ => {  0 } ,
      }
    }
⟧

def expr_has_bvar_at_binder := aiur_fn⟦
  fn expr_has_bvar_at_binder(ty: KernelTypes::KExpr, body: KernelTypes::KExpr, depth: Field) -> Field {
      match expr_has_bvar_at(ty, depth) {
        1 => {  1 } ,
        _ => {  expr_has_bvar_at(body, depth + 1) } ,
      }
    }
⟧

def expr_has_bvar_at_let := aiur_fn⟦
  fn expr_has_bvar_at_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr, depth: Field) -> Field {
      match expr_has_bvar_at(ty, depth) {
        1 => {  1 } ,
        _ => {
          match expr_has_bvar_at(val, depth) {
            1 => {  1 } ,
            _ => {  expr_has_bvar_at(body, depth + 1) } ,
          } } ,
      }
    }
⟧

def expr_inst1 := aiur_fn⟦
  fn expr_inst1(e: KernelTypes::KExpr, arg: KernelTypes::KExpr, depth: Field) -> KernelTypes::KExpr {

      let l = expr_lbr(e);
      match UInt32::less_than_fields(depth, l) {
        0 => {  e } ,
        1 => {
          let do_walk = match UInt32::less_than_fields(depth + 1, l) {
            0 => {  1 } ,
            1 => {  expr_has_bvar_at(e, depth) } ,
          };
          match do_walk {
            1 => {
              match (*(e)) {
                KernelTypes::KExprNode::BVar(_) => {  expr_lift(arg, depth, 0) } ,
                KernelTypes::KExprNode::App(f, a) => {
                  (&(KernelTypes::KExprNode::App(
                    expr_inst1(f, arg, depth),
                    expr_inst1(a, arg, depth)))) } ,
                KernelTypes::KExprNode::Lam(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Lam(
                    expr_inst1(ty, arg, depth),
                    expr_inst1(body, arg, depth + 1), bl))) } ,
                KernelTypes::KExprNode::Forall(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Forall(
                    expr_inst1(ty, arg, depth),
                    expr_inst1(body, arg, depth + 1), bl))) } ,
                KernelTypes::KExprNode::Let(ty, val, body) => {  expr_inst1_let(ty, val, body, arg, depth) } ,
                KernelTypes::KExprNode::Proj(tidx, fidx, e1) => {
                  (&(KernelTypes::KExprNode::Proj(tidx, fidx, expr_inst1(e1, arg, depth)))) } ,
                _ => {  e } ,
              } } ,
            _ => {  expr_lower(e, 1, depth + 1) } ,
          } } ,
      }
    }
⟧

def expr_inst1_let := aiur_fn⟦
  fn expr_inst1_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr, arg: KernelTypes::KExpr, depth: Field)
        -> KernelTypes::KExpr {
      (&(KernelTypes::KExprNode::Let(
        expr_inst1(ty, arg, depth),
        expr_inst1(val, arg, depth),
        expr_inst1(body, arg, depth + 1))))
    }
⟧

def expr_inst_many := aiur_fn⟦
  fn expr_inst_many(e: KernelTypes::KExpr, substs: Lists::List<KernelTypes::KExpr>, depth: Field) -> KernelTypes::KExpr {
      let n = Lists::length(substs);
      match n {
        0 => {  e } ,
        _ => {  expr_inst_many_n(e, substs, n, depth) } ,
      }
    }
⟧

def expr_inst_many_n := aiur_fn⟦
  fn expr_inst_many_n(e: KernelTypes::KExpr, substs: Lists::List<KernelTypes::KExpr>, n: Field, depth: Field) -> KernelTypes::KExpr {
      let l = expr_lbr(e);
      match UInt32::less_than_fields(depth, l) {
        0 => {  e } ,
        1 => {
          let do_walk = match UInt32::less_than_fields(depth + n, l) {
            0 => {  1 } ,
            1 => {  has_bvar_in_range(e, depth, depth + n) } ,
          };
          match do_walk {
            1 => {
              match (*(e)) {
                KernelTypes::KExprNode::BVar(i) => {
                  expr_lift(Lists::lookup(substs, i - depth), depth, 0) } ,
                KernelTypes::KExprNode::App(f, a) => {
                  (&(KernelTypes::KExprNode::App(
                    expr_inst_many_n(f, substs, n, depth),
                    expr_inst_many_n(a, substs, n, depth)))) } ,
                KernelTypes::KExprNode::Lam(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Lam(
                    expr_inst_many_n(ty, substs, n, depth),
                    expr_inst_many_n(body, substs, n, depth + 1), bl))) } ,
                KernelTypes::KExprNode::Forall(ty, body, bl) => {
                  (&(KernelTypes::KExprNode::Forall(
                    expr_inst_many_n(ty, substs, n, depth),
                    expr_inst_many_n(body, substs, n, depth + 1), bl))) } ,
                KernelTypes::KExprNode::Let(ty, val, body) => {
                  expr_inst_many_let(ty, val, body, substs, n, depth) } ,
                KernelTypes::KExprNode::Proj(tidx, fidx, e1) => {
                  (&(KernelTypes::KExprNode::Proj(tidx, fidx, expr_inst_many_n(e1, substs, n, depth)))) } ,
                _ => {  e } ,
              } } ,
            _ => {  expr_lower(e, n, depth + n) } ,
          } } ,
      }
    }
⟧

def expr_inst_many_let := aiur_fn⟦
  fn expr_inst_many_let(ty: KernelTypes::KExpr, val: KernelTypes::KExpr, body: KernelTypes::KExpr,
        substs: Lists::List<KernelTypes::KExpr>, n: Field, depth: Field) -> KernelTypes::KExpr {
      (&(KernelTypes::KExprNode::Let(
        expr_inst_many_n(ty, substs, n, depth),
        expr_inst_many_n(val, substs, n, depth),
        expr_inst_many_n(body, substs, n, depth + 1))))
    }
⟧

  -- `e` with every `Const(a, Nil)` replaced by `v`, at every position: binder domains, `let`
  -- types and values, projection arguments. `v` is closed, so it is shared under binders as it
  -- is. An occurrence of `a` with universe levels is refused, and so is a projection whose
  -- structure is `a` (a projection's structure is an inductive; `a` is an operation, a
  -- definition): no cell naming `a` remains.

def subst_const := aiur_fn⟦
  fn subst_const(e: KernelTypes::KExpr, a: Bytes::AddressRef, v: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Const(c, ls) => {
          match Bytes::address_eq(c, a) {
            1 => {
              match (*(ls)) {
                Lists::Node::Nil => {  v } ,
                Lists::Node::Cons(_, _) => {
                  assert_eq!(0, 1, "an operation occurs with universe levels");
                  e } ,
              } } ,
            _ => {  e } ,
          } } ,
        KernelTypes::KExprNode::App(f, x) => {
          (&(KernelTypes::KExprNode::App(subst_const(f, a, v), subst_const(x, a, v)))) } ,
        KernelTypes::KExprNode::Lam(t, b, bl) => {
          (&(KernelTypes::KExprNode::Lam(subst_const(t, a, v), subst_const(b, a, v), bl))) } ,
        KernelTypes::KExprNode::Forall(t, b, bl) => {
          (&(KernelTypes::KExprNode::Forall(subst_const(t, a, v), subst_const(b, a, v), bl))) } ,
        KernelTypes::KExprNode::Let(t, x, b) => {
          (&(KernelTypes::KExprNode::Let(subst_const(t, a, v), subst_const(x, a, v),
                                          subst_const(b, a, v)))) } ,
        KernelTypes::KExprNode::Proj(s, i, x) => {
          assert_eq!(Bytes::address_eq(s, a), 0, "an operation's certificate projects through the operation");
          (&(KernelTypes::KExprNode::Proj(s, i, subst_const(x, a, v)))) } ,
        _ => {  e } ,
      }
    }
⟧

end

end IxVM
