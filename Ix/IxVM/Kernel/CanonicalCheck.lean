module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Canonical structural ordering of kernel constants

Mirror: src/ix/kernel/canonical_check.rs.

Provides total ordering helpers for `KLevel`, `KExpr`, `KRecRule`, and
`KConstantInfo` so the kernel can verify that mutual blocks ship their
members in canonical (alpha-collapsed, structurally sorted) order. Used
by `validate_canonical_block` adjacent-pair check and by nested-aux
ordering.

Comparator returns G ∈ {0, 1, 2}: 0 = lt, 1 = eq, 2 = gt. Total order
on closed terms (FVars unsupported — Aiur kernel never produces them).
-/

def canonicalCheck := ⟦
  -- ============================================================================
  -- Tri-valued ordering combinators.
  -- 0 = lt, 1 = eq, 2 = gt.
  -- ============================================================================
  fn ord_cmp_g(a: G, b: G) -> G {
    match a - b {
      0 => 1,
      _ =>
        match u32_less_than(a, b) {
          1 => 0,
          0 => 2,
        },
    }
  }

  -- Lexicographic chain: first non-eq wins.
  fn ord_then(a: G, b: G) -> G {
    match a {
      1 => b,
      _ => a,
    }
  }

  -- ============================================================================
  -- SOrd: (ordering, strong) tuple. Mirror of Rust's SOrd. ordering ∈ {0=lt,
  -- 1=eq, 2=gt}; strong ∈ {0=weak, 1=strong}. compare_kexpr_ctx returns SOrd.
  -- Block-local Const refs (resolved via KMutCtx) yield WEAK SOrd; everything
  -- else is STRONG. validate_canonical_block_single_pass accepts strong-Less
  -- directly, falls back to validate_by_refinement on weak-Less.
  -- ============================================================================
  fn sord_lt_strong() -> (G, G) { (0, 1) }
  fn sord_lt_weak() -> (G, G)   { (0, 0) }
  fn sord_eq_strong() -> (G, G) { (1, 1) }
  fn sord_eq_weak() -> (G, G)   { (1, 0) }
  fn sord_gt_strong() -> (G, G) { (2, 1) }

  -- Lex chain on SOrd: if a is Equal, take b's ordering and strong=a.strong*b.strong.
  fn sord_then(a: (G, G), b: (G, G)) -> (G, G) {
    match a {
      (1, sa) =>
        match b {
          (bo, sb) => (bo, sa * sb),
        },
      _ => a,
    }
  }

  -- Wrap a tri-valued G ord as strong SOrd.
  fn sord_of_g(o: G) -> (G, G) { (o, 1) }

  -- ctx_class_idx: returns 1+pos if `idx` ∈ ctx (positional list), else 0.
  -- Mirror: KMutCtx::get(addr) → Option<class_idx>. We use kernel positions
  -- as both addresses and class indices (block members are consecutive in
  -- the kernel `top` layout for our supported block shapes).
  fn ctx_class_idx(idx: G, ctx: List‹G›, i: G) -> G {
    match load(ctx) {
      ListNode.Nil => 0,
      ListNode.Cons(m, rest) =>
        match m - idx {
          0 => 1 + i,
          _ => ctx_class_idx(idx, rest, i + 1),
        },
    }
  }

  -- Compare two Const idxs under a KMutCtx. Strong if both external or
  -- one block-local + one external; weak if both block-local.
  -- Mirror: canonical_check.rs:216-222.
  fn ctx_cmp_idx(xid: G, yid: G, ctx: List‹G›) -> (G, G) {
    let mx = ctx_class_idx(xid, ctx, 0);
    let my = ctx_class_idx(yid, ctx, 0);
    match mx {
      0 =>
        match my {
          0 => sord_of_g(ord_cmp_g(xid, yid)),
          _ => sord_gt_strong(),
        },
      _ =>
        match my {
          0 => sord_lt_strong(),
          _ => (ord_cmp_g(mx, my), 0),
        },
    }
  }

  -- ============================================================================
  -- compare_kuniv
  --
  -- Mirror: canonical_check.rs:130-154. Variant order Zero < Succ < Max <
  -- IMax < Param.
  -- ============================================================================
  fn compare_kuniv(x: KLevel, y: KLevel) -> G {
    match x {
      KLevel.Zero =>
        match y {
          KLevel.Zero => 1,
          _ => 0,
        },
      KLevel.Succ(&xa) =>
        match y {
          KLevel.Zero => 2,
          KLevel.Succ(&ya) => compare_kuniv(xa, ya),
          _ => 0,
        },
      KLevel.Max(&xl, &xr) =>
        match y {
          KLevel.Zero => 2,
          KLevel.Succ(_) => 2,
          KLevel.Max(&yl, &yr) =>
            ord_then(compare_kuniv(xl, yl), compare_kuniv(xr, yr)),
          _ => 0,
        },
      KLevel.IMax(&xl, &xr) =>
        match y {
          KLevel.Zero => 2,
          KLevel.Succ(_) => 2,
          KLevel.Max(_, _) => 2,
          KLevel.IMax(&yl, &yr) =>
            ord_then(compare_kuniv(xl, yl), compare_kuniv(xr, yr)),
          KLevel.Param(_) => 0,
        },
      KLevel.Param(xi) =>
        match y {
          KLevel.Param(yi) => ord_cmp_g(xi, yi),
          _ => 2,
        },
    }
  }

  fn compare_kuniv_list(xs: List‹&KLevel›, ys: List‹&KLevel›) -> G {
    match load(xs) {
      ListNode.Nil =>
        match load(ys) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(&xh, xt) =>
        match load(ys) {
          ListNode.Nil => 2,
          ListNode.Cons(&yh, yt) =>
            ord_then(compare_kuniv(xh, yh), compare_kuniv_list(xt, yt)),
        },
    }
  }

  -- SOrd-returning variant; universes are structural so always strong.
  fn compare_kuniv_list_sord(xs: List‹&KLevel›, ys: List‹&KLevel›) -> (G, G) {
    sord_of_g(compare_kuniv_list(xs, ys))
  }

  -- ============================================================================
  -- compare_kexpr
  --
  -- Mirror: canonical_check.rs:167-275. Variant order BVar < Srt < Const <
  -- App < Lam < Forall < Let < Lit < Proj. Alpha-blind: binders' types
  -- compared, then bodies. (No fvars; Aiur kernel uses de Bruijn indices.)
  -- ============================================================================
  fn compare_kexpr(x: KExpr, y: KExpr) -> G {
    match ptr_val(x) - ptr_val(y) {
      0 => 1,
      _ => compare_kexpr_node(load(x), load(y)),
    }
  }

  fn compare_kexpr_node(x: KExprNode, y: KExprNode) -> G {
    match x {
      KExprNode.BVar(xi) =>
        match y {
          KExprNode.BVar(yi) => ord_cmp_g(xi, yi),
          _ => 0,
        },
      KExprNode.Srt(&xu) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(&yu) => compare_kuniv(xu, yu),
          _ => 0,
        },
      KExprNode.Const(xid, xls) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(_) => 2,
          KExprNode.Const(yid, yls) =>
            ord_then(ord_cmp_g(xid, yid), compare_kuniv_list(xls, yls)),
          _ => 0,
        },
      KExprNode.App(xf, xa) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(_) => 2,
          KExprNode.Const(_, _) => 2,
          KExprNode.App(yf, ya) =>
            ord_then(compare_kexpr(xf, yf), compare_kexpr(xa, ya)),
          _ => 0,
        },
      KExprNode.Lam(xt, xb) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(_) => 2,
          KExprNode.Const(_, _) => 2,
          KExprNode.App(_, _) => 2,
          KExprNode.Lam(yt, yb) =>
            ord_then(compare_kexpr(xt, yt), compare_kexpr(xb, yb)),
          _ => 0,
        },
      KExprNode.Forall(xt, xb) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(_) => 2,
          KExprNode.Const(_, _) => 2,
          KExprNode.App(_, _) => 2,
          KExprNode.Lam(_, _) => 2,
          KExprNode.Forall(yt, yb) =>
            ord_then(compare_kexpr(xt, yt), compare_kexpr(xb, yb)),
          _ => 0,
        },
      KExprNode.Let(xt, xv, xb) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(_) => 2,
          KExprNode.Const(_, _) => 2,
          KExprNode.App(_, _) => 2,
          KExprNode.Lam(_, _) => 2,
          KExprNode.Forall(_, _) => 2,
          KExprNode.Let(yt, yv, yb) =>
            ord_then(compare_kexpr(xt, yt),
              ord_then(compare_kexpr(xv, yv), compare_kexpr(xb, yb))),
          _ => 0,
        },
      KExprNode.Lit(xl) =>
        match y {
          KExprNode.Proj(_, _, _) => 0,
          KExprNode.Lit(yl) => compare_kliteral(xl, yl),
          _ => 2,
        },
      KExprNode.Proj(xt, xf, xe) =>
        match y {
          KExprNode.Proj(yt, yf, ye) =>
            ord_then(ord_cmp_g(xt, yt),
              ord_then(ord_cmp_g(xf, yf), compare_kexpr(xe, ye))),
          _ => 2,
        },
    }
  }

  -- ============================================================================
  -- compare_kexpr_ctx: SOrd-returning, KMutCtx-aware variant.
  -- Mirror: canonical_check.rs:167-280 compare_kexpr.
  -- Const + Proj head ref use ctx_cmp_idx to resolve block-local refs.
  -- Other arms thread ctx into recursive calls.
  -- ============================================================================
  fn compare_kexpr_ctx(x: KExpr, y: KExpr, ctx: List‹G›) -> (G, G) {
    match ptr_val(x) - ptr_val(y) {
      0 => sord_eq_strong(),
      _ => compare_kexpr_node_ctx(load(x), load(y), ctx),
    }
  }

  fn compare_kexpr_node_ctx(x: KExprNode, y: KExprNode, ctx: List‹G›) -> (G, G) {
    match x {
      KExprNode.BVar(xi) =>
        match y {
          KExprNode.BVar(yi) => sord_of_g(ord_cmp_g(xi, yi)),
          _ => sord_lt_strong(),
        },
      KExprNode.Srt(&xu) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(&yu) => sord_of_g(compare_kuniv(xu, yu)),
          _ => sord_lt_strong(),
        },
      KExprNode.Const(xid, xls) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(yid, yls) =>
            sord_then(compare_kuniv_list_sord(xls, yls),
              ctx_cmp_idx(xid, yid, ctx)),
          _ => sord_lt_strong(),
        },
      KExprNode.App(xf, xa) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(_, _) => sord_gt_strong(),
          KExprNode.App(yf, ya) =>
            sord_then(compare_kexpr_ctx(xf, yf, ctx),
                       compare_kexpr_ctx(xa, ya, ctx)),
          _ => sord_lt_strong(),
        },
      KExprNode.Lam(xt, xb) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(_, _) => sord_gt_strong(),
          KExprNode.App(_, _) => sord_gt_strong(),
          KExprNode.Lam(yt, yb) =>
            sord_then(compare_kexpr_ctx(xt, yt, ctx),
                       compare_kexpr_ctx(xb, yb, ctx)),
          _ => sord_lt_strong(),
        },
      KExprNode.Forall(xt, xb) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(_, _) => sord_gt_strong(),
          KExprNode.App(_, _) => sord_gt_strong(),
          KExprNode.Lam(_, _) => sord_gt_strong(),
          KExprNode.Forall(yt, yb) =>
            sord_then(compare_kexpr_ctx(xt, yt, ctx),
                       compare_kexpr_ctx(xb, yb, ctx)),
          _ => sord_lt_strong(),
        },
      KExprNode.Let(xt, xv, xb) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(_, _) => sord_gt_strong(),
          KExprNode.App(_, _) => sord_gt_strong(),
          KExprNode.Lam(_, _) => sord_gt_strong(),
          KExprNode.Forall(_, _) => sord_gt_strong(),
          KExprNode.Let(yt, yv, yb) =>
            sord_then(compare_kexpr_ctx(xt, yt, ctx),
              sord_then(compare_kexpr_ctx(xv, yv, ctx),
                         compare_kexpr_ctx(xb, yb, ctx))),
          _ => sord_lt_strong(),
        },
      KExprNode.Lit(xl) =>
        match y {
          KExprNode.Proj(_, _, _) => sord_lt_strong(),
          KExprNode.Lit(yl) => sord_of_g(compare_kliteral(xl, yl)),
          _ => sord_gt_strong(),
        },
      KExprNode.Proj(xt, xf, xe) =>
        match y {
          KExprNode.Proj(yt, yf, ye) =>
            sord_then(ctx_cmp_idx(xt, yt, ctx),
              sord_then(sord_of_g(ord_cmp_g(xf, yf)),
                         compare_kexpr_ctx(xe, ye, ctx))),
          _ => sord_gt_strong(),
        },
    }
  }

  -- KLiteral order: Nat < Str. Within each, lex on contents.
  fn compare_kliteral(x: KLiteral, y: KLiteral) -> G {
    match x {
      KLiteral.Nat(xn) =>
        match y {
          KLiteral.Nat(yn) => compare_klimbs(xn, yn),
          KLiteral.Str(_) => 0,
        },
      KLiteral.Str(xb) =>
        match y {
          KLiteral.Nat(_) => 2,
          KLiteral.Str(yb) => compare_byte_stream(xb, yb),
        },
    }
  }

  -- Compare KLimbs little-endian. Higher limbs more significant; longer
  -- list = larger value. Walk from tail (most significant); with same
  -- length, lex by limb. Simpler: post-normalize, compare lengths first,
  -- then lex the equal-length tails with most-significant first.
  fn compare_klimbs(x: KLimbs, y: KLimbs) -> G {
    let xn = klimbs_normalize(x);
    let yn = klimbs_normalize(y);
    let lx = list_length(xn);
    let ly = list_length(yn);
    let len_ord = ord_cmp_g(lx, ly);
    match len_ord {
      1 => compare_klimbs_tail(xn, yn),
      _ => len_ord,
    }
  }

  -- Compare equal-length KLimbs lex from MOST significant. We have them
  -- LE, so reverse-walk: recurse first, compare current after.
  fn compare_klimbs_tail(x: KLimbs, y: KLimbs) -> G {
    match load(x) {
      ListNode.Nil => 1,
      ListNode.Cons(xh, xt) =>
        match load(y) {
          ListNode.Cons(yh, yt) =>
            let tail_ord = compare_klimbs_tail(xt, yt);
            ord_then(tail_ord, compare_u64_lex(xh, yh)),
        },
    }
  }

  -- Compare two u64 limbs as integers (little-endian byte order).
  fn compare_u64_lex(a: U64, b: U64) -> G {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    -- Most significant byte first.
    ord_then(ord_cmp_g(a7, b7),
      ord_then(ord_cmp_g(a6, b6),
        ord_then(ord_cmp_g(a5, b5),
          ord_then(ord_cmp_g(a4, b4),
            ord_then(ord_cmp_g(a3, b3),
              ord_then(ord_cmp_g(a2, b2),
                ord_then(ord_cmp_g(a1, b1),
                  ord_cmp_g(a0, b0))))))))
  }

  fn compare_byte_stream(x: ByteStream, y: ByteStream) -> G {
    match load(x) {
      ListNode.Nil =>
        match load(y) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(xh, xt) =>
        match load(y) {
          ListNode.Nil => 2,
          ListNode.Cons(yh, yt) =>
            ord_then(ord_cmp_g(xh, yh), compare_byte_stream(xt, yt)),
        },
    }
  }

  -- ============================================================================
  -- compare_krec_rule
  --
  -- Mirror: canonical_check.rs:280-298. Triple lex.
  -- ============================================================================
  fn compare_krec_rule(x: KRecRule, y: KRecRule) -> G {
    match x {
      KRecRule.Mk(xc, xn, xr) =>
        match y {
          KRecRule.Mk(yc, yn, yr) =>
            ord_then(ord_cmp_g(xc, yc),
              ord_then(ord_cmp_g(xn, yn), compare_kexpr(xr, yr))),
        },
    }
  }

  fn compare_krec_rule_list(xs: List‹KRecRule›, ys: List‹KRecRule›) -> G {
    match load(xs) {
      ListNode.Nil =>
        match load(ys) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(xh, xt) =>
        match load(ys) {
          ListNode.Nil => 2,
          ListNode.Cons(yh, yt) =>
            ord_then(compare_krec_rule(xh, yh), compare_krec_rule_list(xt, yt)),
        },
    }
  }

  -- ctx-aware variant: SOrd-returning, threads ctx into compare_kexpr.
  fn compare_krec_rule_ctx(x: KRecRule, y: KRecRule, ctx: List‹G›) -> (G, G) {
    match x {
      KRecRule.Mk(xc, xn, xr) =>
        match y {
          KRecRule.Mk(yc, yn, yr) =>
            sord_then(sord_of_g(ord_cmp_g(xc, yc)),
              sord_then(sord_of_g(ord_cmp_g(xn, yn)),
                         compare_kexpr_ctx(xr, yr, ctx))),
        },
    }
  }

  fn compare_krec_rule_list_ctx(xs: List‹KRecRule›, ys: List‹KRecRule›,
                                 ctx: List‹G›) -> (G, G) {
    match load(xs) {
      ListNode.Nil =>
        match load(ys) {
          ListNode.Nil => sord_eq_strong(),
          _ => sord_lt_strong(),
        },
      ListNode.Cons(xh, xt) =>
        match load(ys) {
          ListNode.Nil => sord_gt_strong(),
          ListNode.Cons(yh, yt) =>
            sord_then(compare_krec_rule_ctx(xh, yh, ctx),
                       compare_krec_rule_list_ctx(xt, yt, ctx)),
        },
    }
  }

  fn compare_g_list(xs: List‹G›, ys: List‹G›) -> G {
    match load(xs) {
      ListNode.Nil =>
        match load(ys) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(xh, xt) =>
        match load(ys) {
          ListNode.Nil => 2,
          ListNode.Cons(yh, yt) =>
            ord_then(ord_cmp_g(xh, yh), compare_g_list(xt, yt)),
        },
    }
  }

  -- ============================================================================
  -- compare_kconst
  --
  -- Mirror: canonical_check.rs:440-543 + kind ordinals. Variant order:
  -- Defn=0, Thm=1, Opaque=2, Quot=3, Axiom=4, Induct=5, Ctor=6, Rec=7.
  -- Tiebreak: per-variant payload comparison.
  -- ============================================================================
  -- Mirror: src/ix/kernel/canonical_check.rs:440-449 kconst_kind_ord.
  -- Defn=0, Indc=1, Recr=2, Ctor=3, Axio=4, Quot=5. (Thm/Opaque are
  -- Defn-flavored; reuse Defn's slot ordering — only Defn/Indc/Recr are
  -- block-eligible per Rust comment.)
  fn kconst_kind_ord(c: KConstantInfo) -> G {
    match c {
      KConstantInfo.Defn(_, _, _, _, _) => 0,
      KConstantInfo.Thm(_, _, _) => 0,
      KConstantInfo.Opaque(_, _, _, _) => 0,
      KConstantInfo.Induct(_, _, _, _, _, _, _, _, _, _) => 1,
      KConstantInfo.Rec(_, _, _, _, _, _, _, _, _, _) => 2,
      KConstantInfo.Ctor(_, _, _, _, _, _, _) => 3,
      KConstantInfo.Axiom(_, _, _) => 4,
      KConstantInfo.Quot(_, _, _) => 5,
    }
  }

  fn compare_kconst(x: KConstantInfo, y: KConstantInfo) -> G {
    let kx = kconst_kind_ord(x);
    let ky = kconst_kind_ord(y);
    let kord = ord_cmp_g(kx, ky);
    match kord {
      1 => compare_kconst_same_kind(x, y),
      _ => kord,
    }
  }

  fn compare_kconst_same_kind(x: KConstantInfo, y: KConstantInfo) -> G {
    match x {
      KConstantInfo.Defn(xn, xt, xv, _xs, _xh) =>
        match y {
          KConstantInfo.Defn(yn, yt, yv, _ys, _yh) =>
            ord_then(ord_cmp_g(xn, yn),
              ord_then(compare_kexpr(xt, yt), compare_kexpr(xv, yv))),
        },
      KConstantInfo.Thm(xn, xt, xv) =>
        match y {
          KConstantInfo.Thm(yn, yt, yv) =>
            ord_then(ord_cmp_g(xn, yn),
              ord_then(compare_kexpr(xt, yt), compare_kexpr(xv, yv))),
        },
      KConstantInfo.Opaque(xn, xt, xv, xu) =>
        match y {
          KConstantInfo.Opaque(yn, yt, yv, yu) =>
            ord_then(ord_cmp_g(xn, yn),
              ord_then(compare_kexpr(xt, yt),
                ord_then(compare_kexpr(xv, yv), ord_cmp_g(xu, yu)))),
        },
      KConstantInfo.Quot(xn, xt, _xk) =>
        match y {
          KConstantInfo.Quot(yn, yt, _yk) =>
            ord_then(ord_cmp_g(xn, yn), compare_kexpr(xt, yt)),
        },
      KConstantInfo.Axiom(xn, xt, xu) =>
        match y {
          KConstantInfo.Axiom(yn, yt, yu) =>
            ord_then(ord_cmp_g(xn, yn),
              ord_then(compare_kexpr(xt, yt), ord_cmp_g(xu, yu))),
        },
      -- Mirror: src/ix/kernel/canonical_check.rs:299-340 compare_kindc
      -- order: (is_rec, is_unsafe, lvls, params, indices, ctors_len, ty, ctors).
      KConstantInfo.Induct(xn, xt, xp, xi, xc, xr, _xrf, xu, _xne, _xa) =>
        match y {
          KConstantInfo.Induct(yn, yt, yp, yi, yc, yr, _yrf, yu, _yne, _ya) =>
            ord_then(ord_cmp_g(xr, yr),
              ord_then(ord_cmp_g(xu, yu),
                ord_then(ord_cmp_g(xn, yn),
                  ord_then(ord_cmp_g(xp, yp),
                    ord_then(ord_cmp_g(xi, yi),
                      ord_then(ord_cmp_g(list_length(xc), list_length(yc)),
                        compare_kexpr(xt, yt))))))),
        },
      -- Mirror: src/ix/kernel/canonical_check.rs:346-368 compare_kctor
      -- order: (lvls, cidx, params, fields, ty). induct_idx + unsafe excluded
      -- from comparator key (see Rust source).
      KConstantInfo.Ctor(xn, xt, _xi, xc, xp, xf, _xu) =>
        match y {
          KConstantInfo.Ctor(yn, yt, _yi, yc, yp, yf, _yu) =>
            ord_then(ord_cmp_g(xn, yn),
              ord_then(ord_cmp_g(xc, yc),
                ord_then(ord_cmp_g(xp, yp),
                  ord_then(ord_cmp_g(xf, yf), compare_kexpr(xt, yt))))),
        },
      -- Mirror: src/ix/kernel/canonical_check.rs:374-407 compare_krecr
      -- order: (lvls, params, indices, motives, minors, k, ty, rules).
      KConstantInfo.Rec(xn, xt, xp, xi, xm, xmi, xrules, xk, _xu, _xba) =>
        match y {
          KConstantInfo.Rec(yn, yt, yp, yi, ym, ymi, yrules, yk, _yu, _yba) =>
            ord_then(ord_cmp_g(xn, yn),
              ord_then(ord_cmp_g(xp, yp),
                ord_then(ord_cmp_g(xi, yi),
                  ord_then(ord_cmp_g(xm, ym),
                    ord_then(ord_cmp_g(xmi, ymi),
                      ord_then(ord_cmp_g(xk, yk),
                        ord_then(compare_kexpr(xt, yt),
                          compare_krec_rule_list(xrules, yrules)))))))),
        },
    }
  }


  -- ctx-aware variant: SOrd-returning, threads ctx into compare_kexpr_ctx.
  fn compare_kconst_ctx(x: KConstantInfo, y: KConstantInfo,
                        ctx: List‹G›) -> (G, G) {
    let kx = kconst_kind_ord(x);
    let ky = kconst_kind_ord(y);
    let kord = ord_cmp_g(kx, ky);
    match kord {
      1 => compare_kconst_same_kind_ctx(x, y, ctx),
      _ => sord_of_g(kord),
    }
  }

  fn compare_kconst_same_kind_ctx(x: KConstantInfo, y: KConstantInfo,
                                   ctx: List‹G›) -> (G, G) {
    match x {
      KConstantInfo.Defn(xn, xt, xv, _xs, _xh) =>
        match y {
          KConstantInfo.Defn(yn, yt, yv, _ys, _yh) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx),
                         compare_kexpr_ctx(xv, yv, ctx))),
        },
      KConstantInfo.Thm(xn, xt, xv) =>
        match y {
          KConstantInfo.Thm(yn, yt, yv) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx),
                         compare_kexpr_ctx(xv, yv, ctx))),
        },
      KConstantInfo.Opaque(xn, xt, xv, xu) =>
        match y {
          KConstantInfo.Opaque(yn, yt, yv, yu) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx),
                sord_then(compare_kexpr_ctx(xv, yv, ctx),
                           sord_of_g(ord_cmp_g(xu, yu))))),
        },
      KConstantInfo.Quot(xn, xt, _xk) =>
        match y {
          KConstantInfo.Quot(yn, yt, _yk) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)), compare_kexpr_ctx(xt, yt, ctx)),
        },
      KConstantInfo.Axiom(xn, xt, xu) =>
        match y {
          KConstantInfo.Axiom(yn, yt, yu) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx),
                         sord_of_g(ord_cmp_g(xu, yu)))),
        },
      KConstantInfo.Induct(xn, xt, xp, xi, xc, xr, _xrf, xu, _xne, _xa) =>
        match y {
          KConstantInfo.Induct(yn, yt, yp, yi, yc, yr, _yrf, yu, _yne, _ya) =>
            sord_then(sord_of_g(ord_cmp_g(xr, yr)),
              sord_then(sord_of_g(ord_cmp_g(xu, yu)),
                sord_then(sord_of_g(ord_cmp_g(xn, yn)),
                  sord_then(sord_of_g(ord_cmp_g(xp, yp)),
                    sord_then(sord_of_g(ord_cmp_g(xi, yi)),
                      sord_then(sord_of_g(ord_cmp_g(list_length(xc), list_length(yc))),
                        compare_kexpr_ctx(xt, yt, ctx))))))),
        },
      KConstantInfo.Ctor(xn, xt, _xi, xc, xp, xf, _xu) =>
        match y {
          KConstantInfo.Ctor(yn, yt, _yi, yc, yp, yf, _yu) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(sord_of_g(ord_cmp_g(xc, yc)),
                sord_then(sord_of_g(ord_cmp_g(xp, yp)),
                  sord_then(sord_of_g(ord_cmp_g(xf, yf)),
                             compare_kexpr_ctx(xt, yt, ctx))))),
        },
      KConstantInfo.Rec(xn, xt, xp, xi, xm, xmi, xrules, xk, _xu, _xba) =>
        match y {
          KConstantInfo.Rec(yn, yt, yp, yi, ym, ymi, yrules, yk, _yu, _yba) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(sord_of_g(ord_cmp_g(xp, yp)),
                sord_then(sord_of_g(ord_cmp_g(xi, yi)),
                  sord_then(sord_of_g(ord_cmp_g(xm, ym)),
                    sord_then(sord_of_g(ord_cmp_g(xmi, ymi)),
                      sord_then(sord_of_g(ord_cmp_g(xk, yk)),
                        sord_then(compare_kexpr_ctx(xt, yt, ctx),
                                   compare_krec_rule_list_ctx(xrules, yrules, ctx)))))))),
        },
    }
  }

  -- Build ctx (list of kernel positions) for all consts in `top` whose
  -- block_addr equals `target`. Walks `top` once with a position counter.
  fn block_members_of(target: Addr, top: List‹&KConstantInfo›,
                       all_top: List‹&KConstantInfo›, pos: G) -> List‹G› {
    match load(top) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(&ci, rest) =>
        let ba = kconst_block_addr(ci, all_top);
        let rest_members = block_members_of(target, rest, all_top, pos + 1);
        match address_eq(ba, target) {
          1 => store(ListNode.Cons(pos, rest_members)),
          0 => rest_members,
        },
    }
  }

  -- Walks `top` finding adjacent KConstantInfo pairs that share a derived
  -- block_addr. Asserts strict-lt for each such pair. Block_addr derivation:
  --   Induct → its own 10th-field block_addr.
  --   Ctor   → parent Induct's block_addr (via induct_idx lookup).
  --   Rec    → block_addr of the parent of its first rule's ctor.
  --   Other  → [0;32] (not part of a Muts block).
  fn check_canonical_block_sort(top: List‹&KConstantInfo›) {
    check_canonical_block_sort_walk(top, store([0; 32]), store(ListNode.Nil), 0, top)
  }

  fn kconst_block_addr(ci: KConstantInfo, top: List‹&KConstantInfo›) -> Addr {
    match ci {
      KConstantInfo.Induct(_, _, _, _, _, _, _, _, _, ba) => ba,
      KConstantInfo.Ctor(_, _, induct_idx, _, _, _, _) =>
        let ind_ci = load(list_lookup(top, induct_idx));
        match ind_ci {
          KConstantInfo.Induct(_, _, _, _, _, _, _, _, _, ba) => ba,
          _ => store([0; 32]),
        },
      KConstantInfo.Rec(_, _, _, _, _, _, _, _, _, ba) => ba,
      _ => store([0; 32]),
    }
  }

  -- Walk top, group consecutive consts sharing a non-zero block_addr,
  -- and validate each block via iterative refinement.
  fn check_canonical_block_sort_walk(consts: List‹&KConstantInfo›,
                                     cur_ba: Addr,
                                     cur_members: List‹G›,
                                     pos: G,
                                     top: List‹&KConstantInfo›) {
    match load(consts) {
      ListNode.Nil => validate_block_if_nonzero(cur_ba, cur_members, top),
      ListNode.Cons(&ci, rest) =>
        let ba = kconst_block_addr(ci, top);
        match address_eq(ba, cur_ba) {
          1 =>
            check_canonical_block_sort_walk(rest, ba, list_snoc(cur_members, pos),
                                             pos + 1, top),
          0 =>
            let _ = validate_block_if_nonzero(cur_ba, cur_members, top);
            let new_members = init_block_members(ba, pos);
            check_canonical_block_sort_walk(rest, ba, new_members, pos + 1, top),
        },
    }
  }

  fn init_block_members(ba: Addr, pos: G) -> List‹G› {
    match address_eq(ba, store([0; 32])) {
      1 => store(ListNode.Nil),
      0 => store(ListNode.Cons(pos, store(ListNode.Nil))),
    }
  }

  fn validate_block_if_nonzero(ba: Addr, members: List‹G›,
                                top: List‹&KConstantInfo›) {
    match address_eq(ba, store([0; 32])) {
      1 => (),
      0 =>
        match list_length(members) {
          0 => (),
          1 => (),
          _ => validate_block_canonical(members, top),
        },
    }
  }

  -- Mirror: src/ix/kernel/canonical_check.rs:732-762 validate_by_full_refinement.
  -- Run sort_kconsts, assert all classes are singletons, and stored order
  -- matches the canonical sort. Equal classes (size > 1) signal an alpha-
  -- collision in the block — Lean's compiler should have collapsed those.
  -- Mirror Rust ingress.rs:2025-2048: validate canonical order for
  -- Indc subset only. Ctors share parent's block_addr in our walk but
  -- aren't actual block members per Rust's KConst::Indc.block field.
  fn validate_block_canonical(stored: List‹G›, top: List‹&KConstantInfo›) {
    let stored_indcs = filter_indc_positions(stored, top);
    match list_length(stored_indcs) {
      0 => (),
      1 => (),
      _ =>
        let classes = sort_kconsts(stored_indcs, top);
        let sing = all_singleton_classes(classes);
        let sorted = flatten_classes(classes);
        let eq = g_list_eq(sorted, stored_indcs);
        assert_eq!(sing, 1);
        assert_eq!(eq, 1);
        (),
    }
  }

  fn filter_indc_positions(positions: List‹G›,
                           top: List‹&KConstantInfo›) -> List‹G› {
    match load(positions) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(p, rest) =>
        let ci = load(list_lookup(top, p));
        let rest_filtered = filter_indc_positions(rest, top);
        match kconst_kind_ord(ci) {
          1 => store(ListNode.Cons(p, rest_filtered)),
          _ => rest_filtered,
        },
    }
  }

  fn all_singleton_classes(classes: List‹List‹G››) -> G {
    match load(classes) {
      ListNode.Nil => 1,
      ListNode.Cons(c, rest) =>
        match list_length(c) {
          1 => all_singleton_classes(rest),
          _ => 0,
        },
    }
  }

  fn flatten_classes(classes: List‹List‹G››) -> List‹G› {
    match load(classes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, rest) =>
        list_concat(c, flatten_classes(rest)),
    }
  }

  fn g_list_eq(xs: List‹G›, ys: List‹G›) -> G {
    match load(xs) {
      ListNode.Nil =>
        match load(ys) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(x, xt) =>
        match load(ys) {
          ListNode.Nil => 0,
          ListNode.Cons(y, yt) =>
            match x - y {
              0 => g_list_eq(xt, yt),
              _ => 0,
            },
        },
    }
  }

  -- ============================================================================
  -- Iterative refinement: sort_kconsts (mirror canonical_check.rs:657-703).
  --
  -- Seed: members sorted by kernel position (stable seed key in our layout).
  -- Loop:
  --   1. ctx = flatten of current classes.
  --   2. For each multi-element class: sort by compare_kconst_ctx, then
  --      group consecutive equals.
  --   3. If new partition equals previous: done.
  -- ============================================================================
  fn sort_kconsts(members: List‹G›, top: List‹&KConstantInfo›) -> List‹List‹G›› {
    -- Seed: single class with members in given order (kernel positions are
    -- already a stable seed key).
    let seed = store(ListNode.Cons(members, store(ListNode.Nil)));
    sort_kconsts_loop(seed, top, 32)
  }

  fn sort_kconsts_loop(classes: List‹List‹G››, top: List‹&KConstantInfo›,
                        fuel: G) -> List‹List‹G›› {
    match fuel {
      0 => classes,
      _ =>
        let ctx = flatten_classes(classes);
        let new_classes = refine_classes(classes, ctx, top);
        match classes_eq(classes, new_classes) {
          1 => classes,
          _ => sort_kconsts_loop(new_classes, top, fuel - 1),
        },
    }
  }

  fn refine_classes(classes: List‹List‹G››, ctx: List‹G›,
                     top: List‹&KConstantInfo›) -> List‹List‹G›› {
    match load(classes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, rest) =>
        let refined = refine_one_class(c, ctx, top);
        list_concat(refined, refine_classes(rest, ctx, top)),
    }
  }

  fn refine_one_class(c: List‹G›, ctx: List‹G›,
                       top: List‹&KConstantInfo›) -> List‹List‹G›› {
    match list_length(c) {
      0 => store(ListNode.Nil),
      1 => store(ListNode.Cons(c, store(ListNode.Nil))),
      _ =>
        let sorted = insertion_sort_class(c, ctx, top);
        group_consecutive_class(sorted, ctx, top),
    }
  }

  fn insertion_sort_class(xs: List‹G›, ctx: List‹G›,
                           top: List‹&KConstantInfo›) -> List‹G› {
    match load(xs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(x, rest) =>
        insert_sorted(x, insertion_sort_class(rest, ctx, top), ctx, top),
    }
  }

  fn insert_sorted(x: G, sorted: List‹G›, ctx: List‹G›,
                    top: List‹&KConstantInfo›) -> List‹G› {
    match load(sorted) {
      ListNode.Nil => store(ListNode.Cons(x, store(ListNode.Nil))),
      ListNode.Cons(h, rest) =>
        match compare_kconst_ctx(load(list_lookup(top, x)),
                                  load(list_lookup(top, h)), ctx) {
          (0, _) => store(ListNode.Cons(x, sorted)),
          _ => store(ListNode.Cons(h, insert_sorted(x, rest, ctx, top))),
        },
    }
  }

  fn group_consecutive_class(sorted: List‹G›, ctx: List‹G›,
                              top: List‹&KConstantInfo›) -> List‹List‹G›› {
    match load(sorted) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(h, rest) =>
        group_consecutive_walk(rest, ctx, top, h,
                                store(ListNode.Cons(h, store(ListNode.Nil)))),
    }
  }

  fn group_consecutive_walk(remaining: List‹G›, ctx: List‹G›,
                             top: List‹&KConstantInfo›,
                             last: G, current_group: List‹G›) -> List‹List‹G›› {
    match load(remaining) {
      ListNode.Nil => store(ListNode.Cons(current_group, store(ListNode.Nil))),
      ListNode.Cons(h, rest) =>
        match compare_kconst_ctx(load(list_lookup(top, last)),
                                  load(list_lookup(top, h)), ctx) {
          (1, _) =>
            group_consecutive_walk(rest, ctx, top, h, list_snoc(current_group, h)),
          _ =>
            store(ListNode.Cons(current_group,
              group_consecutive_walk(rest, ctx, top, h,
                store(ListNode.Cons(h, store(ListNode.Nil)))))),
        },
    }
  }

  fn classes_eq(a: List‹List‹G››, b: List‹List‹G››) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(ah, arest) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(bh, brest) =>
            match g_list_eq(ah, bh) {
              0 => 0,
              _ => classes_eq(arest, brest),
            },
        },
    }
  }
⟧

end IxVM

end
