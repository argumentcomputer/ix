/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.IxVM.Certified.Expr

/-!
Aiur implementation of the C2 rule checks in
`Ix.Theory.Certified.Checker`. The checked endpoints and intermediate terms are
untrusted data. Assertions and pattern failures abort; the sole successful
result is unit. The backend reflection theorem remains a separate obligation.
-/

namespace IxVM.Certified

def checker := ⟦
  fn c_type(fuel: G, n: G, env: CEnv, ctx: CCtx, e: CExpr, a: CExpr, w: CType) {
    c_fuel(fuel);
    let depth = c_len(192, ctx);
    c_scope(192, n, depth, e); c_scope(192, n, depth, a);
    match load(w) {
      CTypeNode.Srt =>
        let CExprNode.Srt(l) = load(e);
        assert_eq!(c_expr_eq(192, 1, a, store(CExprNode.Srt(store(CLevelNode.Succ(l))))), 1); (),
      CTypeNode.BVar =>
        let CExprNode.BVar(i) = load(e);
        assert_eq!(c_expr_eq(192, 1, a, c_at(192, ctx, i)), 1); (),
      CTypeNode.Const =>
        let CExprNode.Const(r, ls) = load(e);
        let Option.Some(CEntry.Mk(_, m, typ, _)) = c_lookup(192, env, r);
        assert_eq!(c_len(192, ls), m);
        assert_eq!(c_expr_eq(192, 1, a, c_inst_levels(192, ls, typ)), 1); (),
      CTypeNode.App(p, d, b, wf, wa) =>
        let CExprNode.App(f, arg) = load(e);
        assert_eq!(c_expr_eq(192, 1, a, c_inst(192, 0, arg, b)), 1);
        c_type(fuel - 1, n, env, ctx, f, store(CExprNode.Pi(p, d, b)), wf);
        c_type(fuel - 1, n, env, ctx, arg, d, wa),
      CTypeNode.Lam(ld, lb, b, wd, wb, wt) =>
        let CExprNode.Lam(p, d, body) = load(e);
        assert_eq!(c_when_eq(192, p, c_zero_condition(192, lb)), 1);
        assert_eq!(c_expr_eq(192, 1, a, store(CExprNode.Pi(p, d, b))), 1);
        c_type(fuel - 1, n, env, ctx, d, store(CExprNode.Srt(ld)), wd);
        let next = c_push(192, d, ctx);
        c_type(fuel - 1, n, env, next, b, store(CExprNode.Srt(lb)), wb);
        c_type(fuel - 1, n, env, next, body, b, wt),
      CTypeNode.Pi(ld, lb, wd, wb) =>
        let CExprNode.Pi(p, d, b) = load(e);
        assert_eq!(c_when_eq(192, p, c_zero_condition(192, lb)), 1);
        assert_eq!(c_expr_eq(192, 1, a, store(CExprNode.Srt(store(CLevelNode.IMax(ld, lb))))), 1);
        c_type(fuel - 1, n, env, ctx, d, store(CExprNode.Srt(ld)), wd);
        c_type(fuel - 1, n, env, c_push(192, d, ctx), b, store(CExprNode.Srt(lb)), wb),
      CTypeNode.Conv(b, la, we, wa, wc) =>
        c_type(fuel - 1, n, env, ctx, e, b, we);
        c_type(fuel - 1, n, env, ctx, a, store(CExprNode.Srt(la)), wa);
        c_conv(fuel - 1, n, env, ctx, b, a, wc),
    }
  }
  fn c_conv(fuel: G, n: G, env: CEnv, ctx: CCtx, a: CExpr, b: CExpr, w: CConv) {
    c_fuel(fuel);
    let depth = c_len(192, ctx);
    c_scope(192, n, depth, a); c_scope(192, n, depth, b);
    match load(w) {
      CConvNode.Refl => assert_eq!(c_expr_eq(192, 1, a, b), 1); (),
      CConvNode.Symm(w) => c_conv(fuel - 1, n, env, ctx, b, a, w),
      CConvNode.Trans(c, wl, wr) =>
        c_conv(fuel - 1, n, env, ctx, a, c, wl);
        c_conv(fuel - 1, n, env, ctx, c, b, wr),
      CConvNode.App(wf, wa) =>
        let CExprNode.App(f, arg) = load(a);
        let CExprNode.App(g, arg2) = load(b);
        c_conv(fuel - 1, n, env, ctx, f, g, wf);
        c_conv(fuel - 1, n, env, ctx, arg, arg2, wa),
      CConvNode.Lam(ld, wd, wa, wb) =>
        let CExprNode.Lam(p, d, body) = load(a);
        let CExprNode.Lam(q, d2, body2) = load(b);
        assert_eq!(c_when_eq(192, p, q), 1);
        c_type(fuel - 1, n, env, ctx, d, store(CExprNode.Srt(ld)), wd);
        c_conv(fuel - 1, n, env, ctx, d, d2, wa);
        c_conv(fuel - 1, n, env, c_push(192, d, ctx), body, body2, wb),
      CConvNode.Pi(ld, wd, wa, wb) =>
        let CExprNode.Pi(p, d, body) = load(a);
        let CExprNode.Pi(q, d2, body2) = load(b);
        assert_eq!(c_when_eq(192, p, q), 1);
        c_type(fuel - 1, n, env, ctx, d, store(CExprNode.Srt(ld)), wd);
        c_conv(fuel - 1, n, env, ctx, d, d2, wa);
        c_conv(fuel - 1, n, env, c_push(192, d, ctx), body, body2, wb),
      CConvNode.Beta(t, wl, wa) =>
        let CExprNode.App(f, arg) = load(a);
        let CExprNode.Lam(_, d, body) = load(f);
        assert_eq!(c_expr_eq(192, 1, b, c_inst(192, 0, arg, body)), 1);
        c_type(fuel - 1, n, env, ctx, f, t, wl);
        c_type(fuel - 1, n, env, ctx, arg, d, wa),
      CConvNode.Eta(codomain, wf) =>
        let CExprNode.Lam(p, d, body) = load(a);
        let expansion = store(CExprNode.App(c_lift(192, 1, 0, b), store(CExprNode.BVar(0))));
        assert_eq!(c_expr_eq(192, 1, body, expansion), 1);
        c_type(fuel - 1, n, env, ctx, b, store(CExprNode.Pi(p, d, codomain)), wf),
      CConvNode.ProofIrrel(typ, wt, wa, wb) =>
        c_type(fuel - 1, n, env, ctx, typ, store(CExprNode.Srt(store(CLevelNode.Zero))), wt);
        c_type(fuel - 1, n, env, ctx, a, typ, wa);
        c_type(fuel - 1, n, env, ctx, b, typ, wb),
      CConvNode.Delta =>
        let CExprNode.Const(r, ls) = load(a);
        let Option.Some(CEntry.Mk(_, m, _, Option.Some(body))) = c_lookup(192, env, r);
        assert_eq!(c_len(192, ls), m);
        assert_eq!(c_expr_eq(192, 1, b, c_inst_levels(192, ls, body)), 1); (),
      CConvNode.Srt =>
        let CExprNode.Srt(l) = load(a);
        let CExprNode.Srt(m) = load(b);
        assert_eq!(c_level_eq(192, c_level_normalize(192, l), c_level_normalize(192, m)), 1); (),
    }
  }
⟧

end IxVM.Certified
