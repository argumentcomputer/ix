/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.IxVM.Certified.Levels

namespace IxVM.Certified

def expr := ⟦
  fn c_scope(fuel: G, n: G, depth: G, e: CExpr) {
    c_fuel(fuel);
    match load(e) {
      CExprNode.Srt(l) => c_level_wf(fuel - 1, n, l),
      CExprNode.BVar(i) => assert_eq!(u32_less_than(i, depth), 1); (),
      CExprNode.Const(_, ls) => c_levels_wf(fuel - 1, n, ls),
      CExprNode.App(f, a) =>
        c_scope(fuel - 1, n, depth, f); c_scope(fuel - 1, n, depth, a),
      CExprNode.Lam(p, a, b) =>
        c_when_wf(fuel - 1, n, p);
        c_scope(fuel - 1, n, depth, a); c_scope(fuel - 1, n, c_add(depth, 1), b),
      CExprNode.Pi(p, a, b) =>
        c_when_wf(fuel - 1, n, p);
        c_scope(fuel - 1, n, depth, a); c_scope(fuel - 1, n, c_add(depth, 1), b),
    }
  }
  -- `annotations = 0` compares erasures; `1` compares the complete reading.
  -- Comparisons are by content. No decision relies on pointer inequality.
  fn c_expr_eq(fuel: G, annotations: G, a: CExpr, b: CExpr) -> G {
    c_fuel(fuel);
    match (load(a), load(b)) {
      (CExprNode.Srt(l), CExprNode.Srt(m)) => c_level_eq(fuel - 1, l, m),
      (CExprNode.BVar(i), CExprNode.BVar(j)) => c_eq(i, j),
      (CExprNode.Const(r, ls), CExprNode.Const(s, ms)) =>
        c_ref_eq(r, s) * c_levels_eq(fuel - 1, ls, ms),
      (CExprNode.App(f, a), CExprNode.App(g, b)) =>
        c_expr_eq(fuel - 1, annotations, f, g) * c_expr_eq(fuel - 1, annotations, a, b),
      (CExprNode.Lam(p, a, b), CExprNode.Lam(q, c, d)) =>
        let same = match annotations { 0 => 1, 1 => c_when_eq(fuel - 1, p, q), };
        same * c_expr_eq(fuel - 1, annotations, a, c) * c_expr_eq(fuel - 1, annotations, b, d),
      (CExprNode.Pi(p, a, b), CExprNode.Pi(q, c, d)) =>
        let same = match annotations { 0 => 1, 1 => c_when_eq(fuel - 1, p, q), };
        same * c_expr_eq(fuel - 1, annotations, a, c) * c_expr_eq(fuel - 1, annotations, b, d),
      _ => 0,
    }
  }
  fn c_lift(fuel: G, count: G, cutoff: G, e: CExpr) -> CExpr {
    c_fuel(fuel);
    match load(e) {
      CExprNode.Srt(_) => e,
      CExprNode.BVar(i) => match u32_less_than(i, cutoff) {
        1 => e, 0 => store(CExprNode.BVar(c_add(i, count))),
      },
      CExprNode.Const(_, _) => e,
      CExprNode.App(f, a) => store(CExprNode.App(
        c_lift(fuel - 1, count, cutoff, f), c_lift(fuel - 1, count, cutoff, a))),
      CExprNode.Lam(p, a, b) => store(CExprNode.Lam(p,
        c_lift(fuel - 1, count, cutoff, a), c_lift(fuel - 1, count, c_add(cutoff, 1), b))),
      CExprNode.Pi(p, a, b) => store(CExprNode.Pi(p,
        c_lift(fuel - 1, count, cutoff, a), c_lift(fuel - 1, count, c_add(cutoff, 1), b))),
    }
  }
  fn c_inst(fuel: G, cutoff: G, arg: CExpr, e: CExpr) -> CExpr {
    c_fuel(fuel);
    match load(e) {
      CExprNode.Srt(_) => e,
      CExprNode.BVar(i) => match u32_less_than(i, cutoff) {
        1 => e,
        0 => match i - cutoff {
          0 => c_lift(fuel - 1, cutoff, 0, arg),
          _ => store(CExprNode.BVar(i - 1)),
        },
      },
      CExprNode.Const(_, _) => e,
      CExprNode.App(f, a) => store(CExprNode.App(
        c_inst(fuel - 1, cutoff, arg, f), c_inst(fuel - 1, cutoff, arg, a))),
      CExprNode.Lam(p, a, b) => store(CExprNode.Lam(p,
        c_inst(fuel - 1, cutoff, arg, a), c_inst(fuel - 1, c_add(cutoff, 1), arg, b))),
      CExprNode.Pi(p, a, b) => store(CExprNode.Pi(p,
        c_inst(fuel - 1, cutoff, arg, a), c_inst(fuel - 1, c_add(cutoff, 1), arg, b))),
    }
  }
  fn c_inst_levels(fuel: G, ls: List‹CLevel›, e: CExpr) -> CExpr {
    c_fuel(fuel);
    match load(e) {
      CExprNode.Srt(l) => store(CExprNode.Srt(c_level_inst(fuel - 1, ls, l))),
      CExprNode.BVar(_) => e,
      CExprNode.Const(r, ms) => store(CExprNode.Const(r, c_levels_inst(fuel - 1, ls, ms))),
      CExprNode.App(f, a) => store(CExprNode.App(
        c_inst_levels(fuel - 1, ls, f), c_inst_levels(fuel - 1, ls, a))),
      CExprNode.Lam(p, a, b) => store(CExprNode.Lam(c_when_inst(fuel - 1, ls, p),
        c_inst_levels(fuel - 1, ls, a), c_inst_levels(fuel - 1, ls, b))),
      CExprNode.Pi(p, a, b) => store(CExprNode.Pi(c_when_inst(fuel - 1, ls, p),
        c_inst_levels(fuel - 1, ls, a), c_inst_levels(fuel - 1, ls, b))),
    }
  }
  fn c_lift_context(fuel: G, ctx: CCtx) -> CCtx {
    c_fuel(fuel);
    match load(ctx) {
      ListNode.Nil => ctx,
      ListNode.Cons(a, tail) => store(ListNode.Cons(
        c_lift(fuel - 1, 1, 0, a), c_lift_context(fuel - 1, tail))),
    }
  }
  fn c_push(fuel: G, a: CExpr, ctx: CCtx) -> CCtx {
    store(ListNode.Cons(c_lift(fuel, 1, 0, a), c_lift_context(fuel, ctx)))
  }
  fn c_lookup(fuel: G, env: CEnv, r: CRef) -> Option‹CEntry› {
    c_fuel(fuel);
    match load(env) {
      ListNode.Nil => Option.None,
      ListNode.Cons(entry, tail) =>
        let CEntry.Mk(s, _, _, _) = entry;
        match c_ref_eq(r, s) {
          1 => Option.Some(entry),
          0 => c_lookup(fuel - 1, tail, r),
        },
    }
  }
  fn c_references(fuel: G, env: CEnv, e: CExpr) {
    c_fuel(fuel);
    match load(e) {
      CExprNode.Srt(_) => (),
      CExprNode.BVar(_) => (),
      CExprNode.Const(r, _) => let Option.Some(_) = c_lookup(fuel - 1, env, r); (),
      CExprNode.App(f, a) =>
        c_references(fuel - 1, env, f); c_references(fuel - 1, env, a),
      CExprNode.Lam(_, a, b) =>
        c_references(fuel - 1, env, a); c_references(fuel - 1, env, b),
      CExprNode.Pi(_, a, b) =>
        c_references(fuel - 1, env, a); c_references(fuel - 1, env, b),
    }
  }
⟧

end IxVM.Certified
