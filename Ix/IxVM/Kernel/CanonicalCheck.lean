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

  -- KMutCtx mirror: a list of (kernel position, class index) pairs.
  -- Mirror: canonical_check.rs:100-118 KMutCtx::from_id_classes — every
  -- member of class j maps to j (same-class members share ONE index, so
  -- refs to them compare weak-Equal, never a position-derived tiebreak),
  -- and every ctor of an Indc member maps to i + cidx where i starts at
  -- |classes| and advances by each class's max ctor count.
  -- ctx_class_idx: returns 1+class_idx if `idx` ∈ ctx, else 0.
  fn ctx_class_idx(idx: G, ctx: List‹(G, G)›) -> G {
    match load(ctx) {
      ListNode.Nil => 0,
      ListNode.Cons(entry, rest) =>
        match entry {
          (pos, j) =>
            match pos - idx {
              0 => 1 + j,
              _ => ctx_class_idx(idx, rest),
            },
        },
    }
  }

  -- Lexicographic compare of two 32-byte addresses (mirror: Rust
  -- `Address`'s derived `Ord`). Packs 4 bytes big-endian per chunk so
  -- 8 u32 comparisons decide; packing preserves byte-lex order.
  fn addr_cmp(x: Addr, y: Addr) -> G {
    let xa = load(x);
    let ya = load(y);
    ord_then(addr_cmp_chunk(to_field(xa[0]), to_field(xa[1]), to_field(xa[2]), to_field(xa[3]),
                            to_field(ya[0]), to_field(ya[1]), to_field(ya[2]), to_field(ya[3])),
      ord_then(addr_cmp_chunk(to_field(xa[4]), to_field(xa[5]), to_field(xa[6]), to_field(xa[7]),
                              to_field(ya[4]), to_field(ya[5]), to_field(ya[6]), to_field(ya[7])),
        ord_then(addr_cmp_chunk(to_field(xa[8]), to_field(xa[9]), to_field(xa[10]), to_field(xa[11]),
                                to_field(ya[8]), to_field(ya[9]), to_field(ya[10]), to_field(ya[11])),
          ord_then(addr_cmp_chunk(to_field(xa[12]), to_field(xa[13]), to_field(xa[14]), to_field(xa[15]),
                                  to_field(ya[12]), to_field(ya[13]), to_field(ya[14]), to_field(ya[15])),
            ord_then(addr_cmp_chunk(to_field(xa[16]), to_field(xa[17]), to_field(xa[18]), to_field(xa[19]),
                                    to_field(ya[16]), to_field(ya[17]), to_field(ya[18]), to_field(ya[19])),
              ord_then(addr_cmp_chunk(to_field(xa[20]), to_field(xa[21]), to_field(xa[22]), to_field(xa[23]),
                                      to_field(ya[20]), to_field(ya[21]), to_field(ya[22]), to_field(ya[23])),
                ord_then(addr_cmp_chunk(to_field(xa[24]), to_field(xa[25]), to_field(xa[26]), to_field(xa[27]),
                                        to_field(ya[24]), to_field(ya[25]), to_field(ya[26]), to_field(ya[27])),
                          addr_cmp_chunk(to_field(xa[28]), to_field(xa[29]), to_field(xa[30]), to_field(xa[31]),
                                         to_field(ya[28]), to_field(ya[29]), to_field(ya[30]), to_field(ya[31])))))))))
  }

  fn addr_cmp_chunk(x0: G, x1: G, x2: G, x3: G,
                    y0: G, y1: G, y2: G, y3: G) -> G {
    let xv = x0 * 16777216 + x1 * 65536 + x2 * 256 + x3;
    let yv = y0 * 16777216 + y1 * 65536 + y2 * 256 + y3;
    ord_cmp_g(xv, yv)
  }

  -- Compare two Const position refs under a KMutCtx.
  -- Mirror: canonical_check.rs:213-222 — same ref ⇒ Equal strong; both
  -- block-local ⇒ weak cmp of class indices (same class ⇒ weak Equal);
  -- one local ⇒ local < external, strong; both external ⇒ strong cmp of
  -- ADDRESSES (kernel analogue of compare_external_refs — NOT ingress
  -- positions, which have no canonical order).
  fn ctx_cmp_idx(xid: G, yid: G, ctx: List‹(G, G)›, addrs: List‹Addr›) -> (G, G) {
    match xid - yid {
      0 => sord_eq_strong(),
      _ =>
        let mx = ctx_class_idx(xid, ctx);
        let my = ctx_class_idx(yid, ctx);
        match mx {
          0 =>
            match my {
              0 => sord_of_g(addr_cmp(list_lookup(addrs, xid),
                                      list_lookup(addrs, yid))),
              _ => sord_gt_strong(),
            },
          _ =>
            match my {
              0 => sord_lt_strong(),
              _ => (ord_cmp_g(mx, my), 0),
            },
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
    match load(x) {
      KLevelNode.Zero =>
        match load(y) {
          KLevelNode.Zero => 1,
          _ => 0,
        },
      KLevelNode.Succ(xa) =>
        match load(y) {
          KLevelNode.Zero => 2,
          KLevelNode.Succ(ya) => compare_kuniv(xa, ya),
          _ => 0,
        },
      KLevelNode.Max(xl, xr) =>
        match load(y) {
          KLevelNode.Zero => 2,
          KLevelNode.Succ(_) => 2,
          KLevelNode.Max(yl, yr) =>
            ord_then(compare_kuniv(xl, yl), compare_kuniv(xr, yr)),
          _ => 0,
        },
      KLevelNode.IMax(xl, xr) =>
        match load(y) {
          KLevelNode.Zero => 2,
          KLevelNode.Succ(_) => 2,
          KLevelNode.Max(_, _) => 2,
          KLevelNode.IMax(yl, yr) =>
            ord_then(compare_kuniv(xl, yl), compare_kuniv(xr, yr)),
          KLevelNode.Param(_) => 0,
        },
      KLevelNode.Param(xi) =>
        match load(y) {
          KLevelNode.Param(yi) => ord_cmp_g(xi, yi),
          _ => 2,
        },
    }
  }

  fn compare_kuniv_list(xs: List‹KLevel›, ys: List‹KLevel›) -> G {
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
            ord_then(compare_kuniv(xh, yh), compare_kuniv_list(xt, yt)),
        },
    }
  }

  -- SOrd-returning variant; universes are structural so always strong.
  fn compare_kuniv_list_sord(xs: List‹KLevel›, ys: List‹KLevel›) -> (G, G) {
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
      KExprNode.Srt(xu) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(yu) => compare_kuniv(xu, yu),
          _ => 0,
        },
      KExprNode.Const(xid, xls) =>
        match y {
          KExprNode.BVar(_) => 2,
          KExprNode.Srt(_) => 2,
          KExprNode.Const(yid, yls) =>
            -- Mirror: canonical_check.rs:204-223 — levels first, then ref.
            -- (Position stands in for the address here; fine for the
            -- equality-only callers of this ctx-less comparator.)
            ord_then(compare_kuniv_list(xls, yls), ord_cmp_g(xid, yid)),
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
  fn compare_kexpr_ctx(x: KExpr, y: KExpr, ctx: List‹(G, G)›,
                       addrs: List‹Addr›) -> (G, G) {
    match ptr_val(x) - ptr_val(y) {
      0 => sord_eq_strong(),
      _ => compare_kexpr_node_ctx(load(x), load(y), ctx, addrs),
    }
  }

  fn compare_kexpr_node_ctx(x: KExprNode, y: KExprNode, ctx: List‹(G, G)›,
                            addrs: List‹Addr›) -> (G, G) {
    match x {
      KExprNode.BVar(xi) =>
        match y {
          KExprNode.BVar(yi) => sord_of_g(ord_cmp_g(xi, yi)),
          _ => sord_lt_strong(),
        },
      KExprNode.Srt(xu) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(yu) => sord_of_g(compare_kuniv(xu, yu)),
          _ => sord_lt_strong(),
        },
      KExprNode.Const(xid, xls) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(yid, yls) =>
            sord_then(compare_kuniv_list_sord(xls, yls),
              ctx_cmp_idx(xid, yid, ctx, addrs)),
          _ => sord_lt_strong(),
        },
      KExprNode.App(xf, xa) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(_, _) => sord_gt_strong(),
          KExprNode.App(yf, ya) =>
            sord_then(compare_kexpr_ctx(xf, yf, ctx, addrs),
                       compare_kexpr_ctx(xa, ya, ctx, addrs)),
          _ => sord_lt_strong(),
        },
      KExprNode.Lam(xt, xb) =>
        match y {
          KExprNode.BVar(_) => sord_gt_strong(),
          KExprNode.Srt(_) => sord_gt_strong(),
          KExprNode.Const(_, _) => sord_gt_strong(),
          KExprNode.App(_, _) => sord_gt_strong(),
          KExprNode.Lam(yt, yb) =>
            sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                       compare_kexpr_ctx(xb, yb, ctx, addrs)),
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
            sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                       compare_kexpr_ctx(xb, yb, ctx, addrs)),
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
            sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
              sord_then(compare_kexpr_ctx(xv, yv, ctx, addrs),
                         compare_kexpr_ctx(xb, yb, ctx, addrs))),
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
            sord_then(ctx_cmp_idx(xt, yt, ctx, addrs),
              sord_then(sord_of_g(ord_cmp_g(xf, yf)),
                         compare_kexpr_ctx(xe, ye, ctx, addrs))),
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
    ord_then(ord_cmp_g(to_field(a7), to_field(b7)),
      ord_then(ord_cmp_g(to_field(a6), to_field(b6)),
        ord_then(ord_cmp_g(to_field(a5), to_field(b5)),
          ord_then(ord_cmp_g(to_field(a4), to_field(b4)),
            ord_then(ord_cmp_g(to_field(a3), to_field(b3)),
              ord_then(ord_cmp_g(to_field(a2), to_field(b2)),
                ord_then(ord_cmp_g(to_field(a1), to_field(b1)),
                  ord_cmp_g(to_field(a0), to_field(b0)))))))))
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
            ord_then(ord_cmp_g(to_field(xh), to_field(yh)), compare_byte_stream(xt, yt)),
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
      KRecRule.Mk(_xc, xn, xr) =>
        match y {
          KRecRule.Mk(_yc, yn, yr) =>
            -- Mirror: canonical_check.rs:280-289 — (fields, rhs) ONLY. The
            -- leading global ctor idx is an ingress artifact with no
            -- canonical meaning; comparing it would order by discovery.
            ord_then(ord_cmp_g(xn, yn), compare_kexpr(xr, yr)),
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
  -- Mirror: canonical_check.rs:280-289 — (fields, rhs) ONLY; the leading
  -- global ctor idx is an ingress artifact (see compare_krec_rule).
  fn compare_krec_rule_ctx(x: KRecRule, y: KRecRule, ctx: List‹(G, G)›,
                           addrs: List‹Addr›) -> (G, G) {
    match x {
      KRecRule.Mk(_xc, xn, xr) =>
        match y {
          KRecRule.Mk(_yc, yn, yr) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
                       compare_kexpr_ctx(xr, yr, ctx, addrs)),
        },
    }
  }

  fn compare_krec_rule_list_ctx(xs: List‹KRecRule›, ys: List‹KRecRule›,
                                 ctx: List‹(G, G)›, addrs: List‹Addr›) -> (G, G) {
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
            sord_then(compare_krec_rule_ctx(xh, yh, ctx, addrs),
                       compare_krec_rule_list_ctx(xt, yt, ctx, addrs)),
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
      KConstantInfo.Induct(_, _, _, _, _, _, _) => 1,
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
      -- PARTIAL mirror of src/ix/kernel/canonical_check.rs compare_kindc:
      -- (is_unsafe, lvls, params, indices, ctors_len, ty) — the ctors[*]
      -- tail is MISSING (needs `top` to resolve ctor positions), so
      -- same-shape mutual inductives compare equal here. This ctx-less
      -- comparator is currently unreachable; the live path is
      -- compare_kconst_ctx, which does compare ctors.
      KConstantInfo.Induct(xn, xt, xp, xi, xc, xu, _xa) =>
        match y {
          KConstantInfo.Induct(yn, yt, yp, yi, yc, yu, _ya) =>
            ord_then(ord_cmp_g(xu, yu),
              ord_then(ord_cmp_g(xn, yn),
                ord_then(ord_cmp_g(xp, yp),
                  ord_then(ord_cmp_g(xi, yi),
                    ord_then(ord_cmp_g(list_length(xc), list_length(yc)),
                      compare_kexpr(xt, yt)))))),
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
  -- `top` is the resolve_ctor analogue: Indc comparison resolves each
  -- ctor position through it (mirror: canonical_check.rs compare_kconst's
  -- `resolve_ctor` parameter). `addrs` backs the external-ref address
  -- compare in ctx_cmp_idx.
  fn compare_kconst_ctx(x: KConstantInfo, y: KConstantInfo,
                        ctx: List‹(G, G)›, top: List‹&KConstantInfo›,
                        addrs: List‹Addr›) -> (G, G) {
    let kx = kconst_kind_ord(x);
    let ky = kconst_kind_ord(y);
    let kord = ord_cmp_g(kx, ky);
    match kord {
      1 => compare_kconst_same_kind_ctx(x, y, ctx, top, addrs),
      _ => sord_of_g(kord),
    }
  }

  fn compare_kconst_same_kind_ctx(x: KConstantInfo, y: KConstantInfo,
                                   ctx: List‹(G, G)›, top: List‹&KConstantInfo›,
                                   addrs: List‹Addr›) -> (G, G) {
    match x {
      KConstantInfo.Defn(xn, xt, xv, _xs, _xh) =>
        match y {
          KConstantInfo.Defn(yn, yt, yv, _ys, _yh) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                         compare_kexpr_ctx(xv, yv, ctx, addrs))),
        },
      KConstantInfo.Thm(xn, xt, xv) =>
        match y {
          KConstantInfo.Thm(yn, yt, yv) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                         compare_kexpr_ctx(xv, yv, ctx, addrs))),
        },
      KConstantInfo.Opaque(xn, xt, xv, xu) =>
        match y {
          KConstantInfo.Opaque(yn, yt, yv, yu) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                sord_then(compare_kexpr_ctx(xv, yv, ctx, addrs),
                           sord_of_g(ord_cmp_g(xu, yu))))),
        },
      KConstantInfo.Quot(xn, xt, _xk) =>
        match y {
          KConstantInfo.Quot(yn, yt, _yk) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
                       compare_kexpr_ctx(xt, yt, ctx, addrs)),
        },
      KConstantInfo.Axiom(xn, xt, xu) =>
        match y {
          KConstantInfo.Axiom(yn, yt, yu) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                         sord_of_g(ord_cmp_g(xu, yu)))),
        },
      -- Mirror: canonical_check.rs:299-338 compare_kindc —
      -- (is_unsafe, lvls, params, indices, |ctors|, ty, ctors[*]).
      -- The ctors tail is what separates same-shape mutual inductives
      -- (e.g. Mathlib's ExBase/ExProd/ExSum: identical flags, arities
      -- and types, differing only in ctor types).
      KConstantInfo.Induct(xn, xt, xp, xi, xc, xu, _xa) =>
        match y {
          KConstantInfo.Induct(yn, yt, yp, yi, yc, yu, _ya) =>
            sord_then(sord_of_g(ord_cmp_g(xu, yu)),
              sord_then(sord_of_g(ord_cmp_g(xn, yn)),
                sord_then(sord_of_g(ord_cmp_g(xp, yp)),
                  sord_then(sord_of_g(ord_cmp_g(xi, yi)),
                    sord_then(sord_of_g(ord_cmp_g(list_length(xc), list_length(yc))),
                      sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                                 compare_kctor_idxs_ctx(xc, yc, ctx, top, addrs))))))),
        },
      KConstantInfo.Ctor(xn, xt, _xi, xc, xp, xf, _xu) =>
        match y {
          KConstantInfo.Ctor(yn, yt, _yi, yc, yp, yf, _yu) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(sord_of_g(ord_cmp_g(xc, yc)),
                sord_then(sord_of_g(ord_cmp_g(xp, yp)),
                  sord_then(sord_of_g(ord_cmp_g(xf, yf)),
                             compare_kexpr_ctx(xt, yt, ctx, addrs))))),
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
                        sord_then(compare_kexpr_ctx(xt, yt, ctx, addrs),
                                   compare_krec_rule_list_ctx(xrules, yrules, ctx, addrs)))))))),
        },
    }
  }

  -- Mirror: canonical_check.rs:322-336 (compare_kindc's ctors tail via
  -- SOrd::try_zip). Walks both ctor-position lists in lockstep, resolving
  -- each position through `top` and comparing the Ctor payloads. List
  -- lengths are compared upstream (|ctors| field), so both lists exhaust
  -- together; the fold mirrors try_zip's lex/weak-propagation semantics.
  fn compare_kctor_idxs_ctx(xs: List‹G›, ys: List‹G›, ctx: List‹(G, G)›,
                             top: List‹&KConstantInfo›, addrs: List‹Addr›) -> (G, G) {
    match load(xs) {
      ListNode.Nil => sord_eq_strong(),
      ListNode.Cons(xpos, xrest) =>
        match load(ys) {
          ListNode.Nil => sord_eq_strong(),
          ListNode.Cons(ypos, yrest) =>
            sord_then(
              compare_kctor_pair_ctx(load(list_lookup(top, xpos)),
                                     load(list_lookup(top, ypos)), ctx, addrs),
              compare_kctor_idxs_ctx(xrest, yrest, ctx, top, addrs)),
        },
    }
  }

  -- Mirror: canonical_check.rs:343-365 compare_kctor —
  -- (lvls, cidx, params, fields, ty); induct_idx + unsafe excluded from
  -- the comparator key. Non-Ctor operands fall back to kind ordering
  -- (comparator stays total on malformed blocks, same as Rust).
  fn compare_kctor_pair_ctx(x: KConstantInfo, y: KConstantInfo,
                             ctx: List‹(G, G)›, addrs: List‹Addr›) -> (G, G) {
    match x {
      KConstantInfo.Ctor(xn, xt, _xi, xc, xp, xf, _xu) =>
        match y {
          KConstantInfo.Ctor(yn, yt, _yi, yc, yp, yf, _yu) =>
            sord_then(sord_of_g(ord_cmp_g(xn, yn)),
              sord_then(sord_of_g(ord_cmp_g(xc, yc)),
                sord_then(sord_of_g(ord_cmp_g(xp, yp)),
                  sord_then(sord_of_g(ord_cmp_g(xf, yf)),
                             compare_kexpr_ctx(xt, yt, ctx, addrs))))),
          _ => sord_of_g(ord_cmp_g(kconst_kind_ord(x), kconst_kind_ord(y))),
        },
      _ => sord_of_g(ord_cmp_g(kconst_kind_ord(x), kconst_kind_ord(y))),
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
  fn check_canonical_block_sort(top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    check_canonical_block_sort_walk(top, store([0u8; 32]), store(ListNode.Nil), 0, top, addrs)
  }

  fn kconst_block_addr(ci: KConstantInfo, top: List‹&KConstantInfo›) -> Addr {
    match ci {
      KConstantInfo.Induct(_, _, _, _, _, _, ba) => ba,
      KConstantInfo.Ctor(_, _, induct_idx, _, _, _, _) =>
        let ind_ci = load(list_lookup(top, induct_idx));
        match ind_ci {
          KConstantInfo.Induct(_, _, _, _, _, _, ba) => ba,
          _ => store([0u8; 32]),
        },
      KConstantInfo.Rec(_, _, _, _, _, _, _, _, _, ba) => ba,
      _ => store([0u8; 32]),
    }
  }

  -- Walk top, group consecutive consts sharing a non-zero block_addr,
  -- and validate each block via iterative refinement.
  fn check_canonical_block_sort_walk(consts: List‹&KConstantInfo›,
                                     cur_ba: Addr,
                                     cur_members: List‹G›,
                                     pos: G,
                                     top: List‹&KConstantInfo›,
                                     addrs: List‹Addr›) {
    match load(consts) {
      ListNode.Nil => validate_block_if_nonzero(cur_ba, cur_members, top, addrs),
      ListNode.Cons(&ci, rest) =>
        let ba = kconst_block_addr(ci, top);
        match address_eq(ba, cur_ba) {
          1 =>
            check_canonical_block_sort_walk(rest, ba, list_snoc(cur_members, pos),
                                             pos + 1, top, addrs),
          0 =>
            validate_block_if_nonzero(cur_ba, cur_members, top, addrs);
            let new_members = init_block_members(ba, pos);
            check_canonical_block_sort_walk(rest, ba, new_members, pos + 1, top, addrs),
        },
    }
  }

  fn init_block_members(ba: Addr, pos: G) -> List‹G› {
    match address_eq(ba, store([0u8; 32])) {
      1 => store(ListNode.Nil),
      0 => store(ListNode.Cons(pos, store(ListNode.Nil))),
    }
  }

  fn validate_block_if_nonzero(ba: Addr, members: List‹G›,
                                top: List‹&KConstantInfo›,
                                addrs: List‹Addr›) {
    match address_eq(ba, store([0u8; 32])) {
      1 => (),
      0 =>
        match list_length(members) {
          0 => (),
          1 => (),
          _ => validate_block_canonical(members, top, addrs),
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
  fn validate_block_canonical(stored: List‹G›, top: List‹&KConstantInfo›,
                              addrs: List‹Addr›) {
    let stored_indcs = filter_indc_positions(stored, top);
    match list_length(stored_indcs) {
      0 => (),
      1 => (),
      _ =>
        let classes = sort_kconsts(stored_indcs, top, addrs);
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
  -- Iterative refinement: sort_kconsts (mirror canonical_check.rs:650-696).
  --
  -- Seed: members in stored order (single class).
  -- Loop:
  --   1. ctx = KMutCtx over current classes (build_mut_ctx).
  --   2. For each multi-element class: sort by compare_kconst_ctx, then
  --      group consecutive equals.
  --   3. If new partition equals previous: done.
  -- Fuel: each non-fixpoint iteration splits ≥1 class and class count is
  -- bounded by |members|, so 1 + |members| iterations always reach the
  -- fixpoint (Rust loops unboundedly; a fixed constant would silently
  -- truncate refinement on very wide blocks).
  -- ============================================================================
  fn sort_kconsts(members: List‹G›, top: List‹&KConstantInfo›,
                  addrs: List‹Addr›) -> List‹List‹G›› {
    let seed = store(ListNode.Cons(members, store(ListNode.Nil)));
    sort_kconsts_loop(seed, top, addrs, 1 + list_length(members))
  }

  fn sort_kconsts_loop(classes: List‹List‹G››, top: List‹&KConstantInfo›,
                        addrs: List‹Addr›, fuel: G) -> List‹List‹G›› {
    match fuel {
      0 => classes,
      _ =>
        let ctx = build_mut_ctx(classes, top);
        let new_classes = refine_classes(classes, ctx, top, addrs);
        match classes_eq(classes, new_classes) {
          1 => classes,
          _ => sort_kconsts_loop(new_classes, top, addrs, fuel - 1),
        },
    }
  }

  -- ============================================================================
  -- KMutCtx builder. Mirror: canonical_check.rs:100-118
  -- KMutCtx::from_id_classes — class members map to their class index j
  -- (ALL members of a class share j, so refs to tied members compare
  -- weak-Equal instead of taking a position-derived tiebreak), and each
  -- Indc member's ctors map to i + cidx, where i starts at |classes| and
  -- advances by each class's max ctor count.
  -- ============================================================================
  fn build_mut_ctx(classes: List‹List‹G››,
                   top: List‹&KConstantInfo›) -> List‹(G, G)› {
    build_mut_ctx_classes(classes, top, 0, list_length(classes))
  }

  fn build_mut_ctx_classes(classes: List‹List‹G››, top: List‹&KConstantInfo›,
                           j: G, i: G) -> List‹(G, G)› {
    match load(classes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(cls, rest) =>
        let (entries, max_ctors) = build_mut_ctx_members(cls, top, j, i);
        list_concat(entries,
                    build_mut_ctx_classes(rest, top, j + 1, i + max_ctors)),
    }
  }

  -- Entries for one class's members (+ their ctors); also returns the
  -- class's max ctor count for the caller's `i` advance.
  fn build_mut_ctx_members(members: List‹G›, top: List‹&KConstantInfo›,
                           j: G, i: G) -> (List‹(G, G)›, G) {
    match load(members) {
      ListNode.Nil => (store(ListNode.Nil), 0),
      ListNode.Cons(pos, rest) =>
        let (rest_entries, rest_max) = build_mut_ctx_members(rest, top, j, i);
        let ctors = kconst_ctor_idxs(load(list_lookup(top, pos)));
        let n = list_length(ctors);
        let ctor_entries = ctor_ctx_entries(ctors, i, 0);
        let entries = store(ListNode.Cons((pos, j),
                            list_concat(ctor_entries, rest_entries)));
        match u32_less_than(rest_max, n) {
          1 => (entries, n),
          _ => (entries, rest_max),
        },
    }
  }

  fn ctor_ctx_entries(ctors: List‹G›, i: G, cidx: G) -> List‹(G, G)› {
    match load(ctors) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(cpos, rest) =>
        store(ListNode.Cons((cpos, i + cidx),
                            ctor_ctx_entries(rest, i, cidx + 1))),
    }
  }

  -- Mirror: canonical_check.rs:73-77 cnst_ctors — Indc's ctor positions,
  -- empty for every other kind.
  fn kconst_ctor_idxs(ci: KConstantInfo) -> List‹G› {
    match ci {
      KConstantInfo.Induct(_, _, _, _, ctor_indices, _, _) => ctor_indices,
      _ => store(ListNode.Nil),
    }
  }

  fn refine_classes(classes: List‹List‹G››, ctx: List‹(G, G)›,
                     top: List‹&KConstantInfo›,
                     addrs: List‹Addr›) -> List‹List‹G›› {
    match load(classes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, rest) =>
        let refined = refine_one_class(c, ctx, top, addrs);
        list_concat(refined, refine_classes(rest, ctx, top, addrs)),
    }
  }

  fn refine_one_class(c: List‹G›, ctx: List‹(G, G)›,
                       top: List‹&KConstantInfo›,
                       addrs: List‹Addr›) -> List‹List‹G›› {
    match list_length(c) {
      0 => store(ListNode.Nil),
      1 => store(ListNode.Cons(c, store(ListNode.Nil))),
      _ =>
        let sorted = insertion_sort_class(c, ctx, top, addrs);
        group_consecutive_class(sorted, ctx, top, addrs),
    }
  }

  fn insertion_sort_class(xs: List‹G›, ctx: List‹(G, G)›,
                           top: List‹&KConstantInfo›,
                           addrs: List‹Addr›) -> List‹G› {
    match load(xs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(x, rest) =>
        insert_sorted(x, insertion_sort_class(rest, ctx, top, addrs), ctx, top, addrs),
    }
  }

  fn insert_sorted(x: G, sorted: List‹G›, ctx: List‹(G, G)›,
                    top: List‹&KConstantInfo›, addrs: List‹Addr›) -> List‹G› {
    match load(sorted) {
      ListNode.Nil => store(ListNode.Cons(x, store(ListNode.Nil))),
      ListNode.Cons(h, rest) =>
        match compare_kconst_ctx(load(list_lookup(top, x)),
                                  load(list_lookup(top, h)), ctx, top, addrs) {
          (0, _) => store(ListNode.Cons(x, sorted)),
          _ => store(ListNode.Cons(h, insert_sorted(x, rest, ctx, top, addrs))),
        },
    }
  }

  fn group_consecutive_class(sorted: List‹G›, ctx: List‹(G, G)›,
                              top: List‹&KConstantInfo›,
                              addrs: List‹Addr›) -> List‹List‹G›› {
    match load(sorted) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(h, rest) =>
        group_consecutive_walk(rest, ctx, top, addrs, h,
                                store(ListNode.Cons(h, store(ListNode.Nil)))),
    }
  }

  fn group_consecutive_walk(remaining: List‹G›, ctx: List‹(G, G)›,
                             top: List‹&KConstantInfo›, addrs: List‹Addr›,
                             last: G, current_group: List‹G›) -> List‹List‹G›› {
    match load(remaining) {
      ListNode.Nil => store(ListNode.Cons(current_group, store(ListNode.Nil))),
      ListNode.Cons(h, rest) =>
        match compare_kconst_ctx(load(list_lookup(top, last)),
                                  load(list_lookup(top, h)), ctx, top, addrs) {
          (1, _) =>
            group_consecutive_walk(rest, ctx, top, addrs, h, list_snoc(current_group, h)),
          _ =>
            store(ListNode.Cons(current_group,
              group_consecutive_walk(rest, ctx, top, addrs, h,
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
