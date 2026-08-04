module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Ingress

public section

namespace IxVM

/-! ## Canonical structural ordering of Muts block members

Mirror of Rust `crates/kernel/src/canonical_check.rs`, re-expressed
addr-first.

A mutual block IS one Muts constant here, so no grouping pass is needed:
validate that each Muts block's Indc members ship in canonical
(alpha-collapsed, structurally sorted) order, via the same iterative
partition refinement the Rust checker uses.

Comparator returns tri-valued G (0=lt, 1=eq, 2=gt) wrapped in SOrd
(ordering, strong). Block-local refs — member projection addrs and
their ctors' CPrj addrs, both of which EMBED the stored member index —
compare WEAK by refinement class so the sort is blind to stored order.
External refs compare strong by 32-byte address lex.

Entry `check_canonical_block(block_addr)` is Aiur-memoized per
block addr: called from every Induct/Rec member check, runs once.
-/

def canonicalCheck := ⟦
  -- ==========================================================================
  -- Tri-valued ordering combinators. 0 = lt, 1 = eq, 2 = gt.
  -- ==========================================================================
  fn canon_ord_cmp_g(a: G, b: G) -> G {
    match a - b {
      0 => 1,
      _ =>
        match u32_less_than(a, b) {
          1 => 0,
          0 => 2,
        },
    }
  }

  fn canon_ord_then(a: G, b: G) -> G {
    match a {
      1 => b,
      _ => a,
    }
  }

  -- SOrd = (ordering, strong). strong ∈ {0=weak, 1=strong}.
  fn canon_sord_lt_strong() -> (G, G) { (0, 1) }
  fn canon_sord_eq_strong() -> (G, G) { (1, 1) }
  fn canon_sord_gt_strong() -> (G, G) { (2, 1) }

  fn canon_sord_then(a: (G, G), b: (G, G)) -> (G, G) {
    match a {
      (1, sa) =>
        match b {
          (bo, sb) => (bo, sa * sb),
        },
      _ => a,
    }
  }

  fn canon_sord_of_g(o: G) -> (G, G) { (o, 1) }

  -- ==========================================================================
  -- 32-byte address lex compare (mirror addr_cmp — 4-byte big-endian
  -- chunks; packing preserves byte-lex order).
  -- ==========================================================================
  fn canon_addr_cmp(x: Addr, y: Addr) -> G {
    let xa = load(x);
    let ya = load(y);
    canon_ord_then(canon_addr_chunk(to_field(xa[0]), to_field(xa[1]), to_field(xa[2]), to_field(xa[3]),
                                to_field(ya[0]), to_field(ya[1]), to_field(ya[2]), to_field(ya[3])),
      canon_ord_then(canon_addr_chunk(to_field(xa[4]), to_field(xa[5]), to_field(xa[6]), to_field(xa[7]),
                                  to_field(ya[4]), to_field(ya[5]), to_field(ya[6]), to_field(ya[7])),
        canon_ord_then(canon_addr_chunk(to_field(xa[8]), to_field(xa[9]), to_field(xa[10]), to_field(xa[11]),
                                    to_field(ya[8]), to_field(ya[9]), to_field(ya[10]), to_field(ya[11])),
          canon_ord_then(canon_addr_chunk(to_field(xa[12]), to_field(xa[13]), to_field(xa[14]), to_field(xa[15]),
                                      to_field(ya[12]), to_field(ya[13]), to_field(ya[14]), to_field(ya[15])),
            canon_ord_then(canon_addr_chunk(to_field(xa[16]), to_field(xa[17]), to_field(xa[18]), to_field(xa[19]),
                                        to_field(ya[16]), to_field(ya[17]), to_field(ya[18]), to_field(ya[19])),
              canon_ord_then(canon_addr_chunk(to_field(xa[20]), to_field(xa[21]), to_field(xa[22]), to_field(xa[23]),
                                          to_field(ya[20]), to_field(ya[21]), to_field(ya[22]), to_field(ya[23])),
                canon_ord_then(canon_addr_chunk(to_field(xa[24]), to_field(xa[25]), to_field(xa[26]), to_field(xa[27]),
                                            to_field(ya[24]), to_field(ya[25]), to_field(ya[26]), to_field(ya[27])),
                              canon_addr_chunk(to_field(xa[28]), to_field(xa[29]), to_field(xa[30]), to_field(xa[31]),
                                             to_field(ya[28]), to_field(ya[29]), to_field(ya[30]), to_field(ya[31])))))))))
  }

  fn canon_addr_chunk(x0: G, x1: G, x2: G, x3: G,
                    y0: G, y1: G, y2: G, y3: G) -> G {
    let xv = x0 * 16777216 + x1 * 65536 + x2 * 256 + x3;
    let yv = y0 * 16777216 + y1 * 65536 + y2 * 256 + y3;
    canon_ord_cmp_g(xv, yv)
  }

  -- ==========================================================================
  -- KMutCtx: addr-keyed. Entries map block-local addrs (member proj
  -- addrs + ctor CPrj addrs) to a class index. Mirror ctx over
  -- ingress positions (canonical_check.rs KMutCtx::from_id_classes).
  -- Returns 1+class if found, 0 otherwise.
  -- ==========================================================================
  fn canon_ctx_class_idx(a: Addr, ctx: List‹(Addr, G)›) -> G {
    match load(ctx) {
      ListNode.Nil => 0,
      ListNode.Cons(entry, rest) =>
        match entry {
          (ea, j) =>
            match address_eq(a, ea) {
              1 => 1 + j,
              _ => canon_ctx_class_idx(a, rest),
            },
        },
    }
  }

  -- Compare two Const addr refs under ctx (mirror ctx_cmp_idx):
  -- same addr ⇒ Equal strong; both block-local ⇒ WEAK cmp of class
  -- indices; one local ⇒ local < external, strong; both external ⇒
  -- strong 32-byte addr cmp.
  fn canon_ctx_cmp_addr(x: Addr, y: Addr, ctx: List‹(Addr, G)›) -> (G, G) {
    match address_eq(x, y) {
      1 => canon_sord_eq_strong(),
      _ =>
        let mx = canon_ctx_class_idx(x, ctx);
        let my = canon_ctx_class_idx(y, ctx);
        match mx {
          0 =>
            match my {
              0 => canon_sord_of_g(canon_addr_cmp(x, y)),
              _ => canon_sord_gt_strong(),
            },
          _ =>
            match my {
              0 => canon_sord_lt_strong(),
              _ => (canon_ord_cmp_g(mx, my), 0),
            },
        },
    }
  }

  -- ==========================================================================
  -- compare_kuniv. Variant order Zero < Succ < Max < IMax < Param.
  -- ==========================================================================
  fn canon_cmp_kuniv(x: KLevel, y: KLevel) -> G {
    match load(x) {
      KLevelNode.Zero =>
        match load(y) {
          KLevelNode.Zero => 1,
          _ => 0,
        },
      KLevelNode.Succ(xa) =>
        match load(y) {
          KLevelNode.Zero => 2,
          KLevelNode.Succ(ya) => canon_cmp_kuniv(xa, ya),
          _ => 0,
        },
      KLevelNode.Max(xl, xr) =>
        match load(y) {
          KLevelNode.Zero => 2,
          KLevelNode.Succ(_) => 2,
          KLevelNode.Max(yl, yr) =>
            canon_ord_then(canon_cmp_kuniv(xl, yl), canon_cmp_kuniv(xr, yr)),
          _ => 0,
        },
      KLevelNode.IMax(xl, xr) =>
        match load(y) {
          KLevelNode.Zero => 2,
          KLevelNode.Succ(_) => 2,
          KLevelNode.Max(_, _) => 2,
          KLevelNode.IMax(yl, yr) =>
            canon_ord_then(canon_cmp_kuniv(xl, yl), canon_cmp_kuniv(xr, yr)),
          KLevelNode.Param(_) => 0,
        },
      KLevelNode.Param(xi) =>
        match load(y) {
          KLevelNode.Param(yi) => canon_ord_cmp_g(xi, yi),
          _ => 2,
        },
    }
  }

  fn canon_cmp_kuniv_list(xs: List‹KLevel›, ys: List‹KLevel›) -> G {
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
            canon_ord_then(canon_cmp_kuniv(xh, yh), canon_cmp_kuniv_list(xt, yt)),
        },
    }
  }

  -- ==========================================================================
  -- Literals: Nat < Str; lex within.
  -- ==========================================================================
  fn canon_cmp_kliteral(x: KLiteral, y: KLiteral) -> G {
    match x {
      KLiteral.Nat(xn) =>
        match y {
          KLiteral.Nat(yn) => canon_cmp_klimbs(xn, yn),
          KLiteral.Str(_) => 0,
        },
      KLiteral.Str(xb) =>
        match y {
          KLiteral.Nat(_) => 2,
          KLiteral.Str(yb) => canon_cmp_bytes(xb, yb),
        },
    }
  }

  fn canon_cmp_klimbs(x: KLimbs, y: KLimbs) -> G {
    let xn = klimbs_normalize(x);
    let yn = klimbs_normalize(y);
    let len_ord = canon_ord_cmp_g(list_length(xn), list_length(yn));
    match len_ord {
      1 => canon_cmp_klimbs_tail(xn, yn),
      _ => len_ord,
    }
  }

  fn canon_cmp_klimbs_tail(x: KLimbs, y: KLimbs) -> G {
    match load(x) {
      ListNode.Nil => 1,
      ListNode.Cons(xh, xt) =>
        match load(y) {
          ListNode.Cons(yh, yt) =>
            let tail_ord = canon_cmp_klimbs_tail(xt, yt);
            canon_ord_then(tail_ord, canon_cmp_u64_lex(xh, yh)),
        },
    }
  }

  fn canon_cmp_u64_lex(a: U64, b: U64) -> G {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    canon_ord_then(canon_ord_cmp_g(to_field(a7), to_field(b7)),
      canon_ord_then(canon_ord_cmp_g(to_field(a6), to_field(b6)),
        canon_ord_then(canon_ord_cmp_g(to_field(a5), to_field(b5)),
          canon_ord_then(canon_ord_cmp_g(to_field(a4), to_field(b4)),
            canon_ord_then(canon_ord_cmp_g(to_field(a3), to_field(b3)),
              canon_ord_then(canon_ord_cmp_g(to_field(a2), to_field(b2)),
                canon_ord_then(canon_ord_cmp_g(to_field(a1), to_field(b1)),
                  canon_ord_cmp_g(to_field(a0), to_field(b0)))))))))
  }

  fn canon_cmp_bytes(x: ByteStream, y: ByteStream) -> G {
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
            canon_ord_then(canon_ord_cmp_g(to_field(xh), to_field(yh)),
                         canon_cmp_bytes(xt, yt)),
        },
    }
  }

  -- ==========================================================================
  -- compare_kexpr_ctx: SOrd, KMutCtx-aware. Variant order BVar < Srt <
  -- Const < App < Lam < Forall < Let < Lit < Proj. Const + Proj struct
  -- refs resolve block-local addrs weak via canon_ctx_cmp_addr.
  -- ==========================================================================
  fn canon_cmp_kexpr_ctx(x: KExpr, y: KExpr, ctx: List‹(Addr, G)›) -> (G, G) {
    match ptr_val(x) - ptr_val(y) {
      0 => canon_sord_eq_strong(),
      _ => canon_cmp_kexpr_node_ctx(load(x), load(y), ctx),
    }
  }

  fn canon_cmp_kexpr_node_ctx(x: KExprNode, y: KExprNode,
                            ctx: List‹(Addr, G)›) -> (G, G) {
    match x {
      KExprNode.BVar(xi) =>
        match y {
          KExprNode.BVar(yi) => canon_sord_of_g(canon_ord_cmp_g(xi, yi)),
          _ => canon_sord_lt_strong(),
        },
      KExprNode.Srt(xu) =>
        match y {
          KExprNode.BVar(_) => canon_sord_gt_strong(),
          KExprNode.Srt(yu) => canon_sord_of_g(canon_cmp_kuniv(xu, yu)),
          _ => canon_sord_lt_strong(),
        },
      KExprNode.Const(xa, xls) =>
        match y {
          KExprNode.BVar(_) => canon_sord_gt_strong(),
          KExprNode.Srt(_) => canon_sord_gt_strong(),
          KExprNode.Const(ya, yls) =>
            canon_sord_then(canon_sord_of_g(canon_cmp_kuniv_list(xls, yls)),
              canon_ctx_cmp_addr(xa, ya, ctx)),
          _ => canon_sord_lt_strong(),
        },
      KExprNode.App(xf, xa) =>
        match y {
          KExprNode.BVar(_) => canon_sord_gt_strong(),
          KExprNode.Srt(_) => canon_sord_gt_strong(),
          KExprNode.Const(_, _) => canon_sord_gt_strong(),
          KExprNode.App(yf, ya) =>
            canon_sord_then(canon_cmp_kexpr_ctx(xf, yf, ctx),
                          canon_cmp_kexpr_ctx(xa, ya, ctx)),
          _ => canon_sord_lt_strong(),
        },
      KExprNode.Lam(xt, xb) =>
        match y {
          KExprNode.BVar(_) => canon_sord_gt_strong(),
          KExprNode.Srt(_) => canon_sord_gt_strong(),
          KExprNode.Const(_, _) => canon_sord_gt_strong(),
          KExprNode.App(_, _) => canon_sord_gt_strong(),
          KExprNode.Lam(yt, yb) =>
            canon_sord_then(canon_cmp_kexpr_ctx(xt, yt, ctx),
                          canon_cmp_kexpr_ctx(xb, yb, ctx)),
          _ => canon_sord_lt_strong(),
        },
      KExprNode.Forall(xt, xb) =>
        match y {
          KExprNode.BVar(_) => canon_sord_gt_strong(),
          KExprNode.Srt(_) => canon_sord_gt_strong(),
          KExprNode.Const(_, _) => canon_sord_gt_strong(),
          KExprNode.App(_, _) => canon_sord_gt_strong(),
          KExprNode.Lam(_, _) => canon_sord_gt_strong(),
          KExprNode.Forall(yt, yb) =>
            canon_sord_then(canon_cmp_kexpr_ctx(xt, yt, ctx),
                          canon_cmp_kexpr_ctx(xb, yb, ctx)),
          _ => canon_sord_lt_strong(),
        },
      KExprNode.Let(xt, xv, xb) =>
        match y {
          KExprNode.BVar(_) => canon_sord_gt_strong(),
          KExprNode.Srt(_) => canon_sord_gt_strong(),
          KExprNode.Const(_, _) => canon_sord_gt_strong(),
          KExprNode.App(_, _) => canon_sord_gt_strong(),
          KExprNode.Lam(_, _) => canon_sord_gt_strong(),
          KExprNode.Forall(_, _) => canon_sord_gt_strong(),
          KExprNode.Let(yt, yv, yb) =>
            canon_sord_then(canon_cmp_kexpr_ctx(xt, yt, ctx),
              canon_sord_then(canon_cmp_kexpr_ctx(xv, yv, ctx),
                            canon_cmp_kexpr_ctx(xb, yb, ctx))),
          _ => canon_sord_lt_strong(),
        },
      KExprNode.Lit(xl) =>
        match y {
          KExprNode.Proj(_, _, _) => canon_sord_lt_strong(),
          KExprNode.Lit(yl) => canon_sord_of_g(canon_cmp_kliteral(xl, yl)),
          _ => canon_sord_gt_strong(),
        },
      KExprNode.Proj(xs, xf, xe) =>
        match y {
          KExprNode.Proj(ys, yf, ye) =>
            canon_sord_then(canon_ctx_cmp_addr(xs, ys, ctx),
              canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xf, yf)),
                            canon_cmp_kexpr_ctx(xe, ye, ctx))),
          _ => canon_sord_gt_strong(),
        },
    }
  }

  -- ==========================================================================
  -- Rec rules: (fields, rhs) only — the leading ctor idx is excluded
  -- from the comparator key (mirror / canonical_check.rs:280-289).
  -- ==========================================================================
  fn canon_cmp_krec_rule_ctx(x: KRecRule, y: KRecRule,
                           ctx: List‹(Addr, G)›) -> (G, G) {
    match x {
      KRecRule.Mk(_xc, xn, xr) =>
        match y {
          KRecRule.Mk(_yc, yn, yr) =>
            canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xn, yn)),
                          canon_cmp_kexpr_ctx(xr, yr, ctx)),
        },
    }
  }

  fn canon_cmp_krec_rule_list_ctx(xs: List‹KRecRule›, ys: List‹KRecRule›,
                                ctx: List‹(Addr, G)›) -> (G, G) {
    match load(xs) {
      ListNode.Nil =>
        match load(ys) {
          ListNode.Nil => canon_sord_eq_strong(),
          _ => canon_sord_lt_strong(),
        },
      ListNode.Cons(xh, xt) =>
        match load(ys) {
          ListNode.Nil => canon_sord_gt_strong(),
          ListNode.Cons(yh, yt) =>
            canon_sord_then(canon_cmp_krec_rule_ctx(xh, yh, ctx),
                          canon_cmp_krec_rule_list_ctx(xt, yt, ctx)),
        },
    }
  }

  -- ==========================================================================
  -- Member comparator. Kind order: Defn(+Thm/Opaque)=0, Indc=1, Recr=2,
  -- Ctor=3, Axiom=4, Quot=5 (mirror kconst_kind_ord).
  -- ==========================================================================
  fn canon_kind_ord(c: KConstantInfo) -> G {
    match c {
      KConstantInfo.Defn(_, _, _, _, _) => 0,
      KConstantInfo.Thm(_, _, _) => 0,
      KConstantInfo.Opaque(_, _, _, _) => 0,
      KConstantInfo.Induct(_, _, _, _, _, _, _, _) => 1,
      KConstantInfo.Rec(_, _, _, _, _, _, _, _, _, _, _) => 2,
      KConstantInfo.Ctor(_, _, _, _, _, _, _, _) => 3,
      KConstantInfo.Axiom(_, _, _) => 4,
      KConstantInfo.Quot(_, _, _) => 5,
    }
  }

  fn canon_cmp_member_ctx(x: KConstantInfo, y: KConstantInfo,
                        ctx: List‹(Addr, G)›) -> (G, G) {
    let kord = canon_ord_cmp_g(canon_kind_ord(x), canon_kind_ord(y));
    match kord {
      1 => canon_cmp_member_same_kind_ctx(x, y, ctx),
      _ => canon_sord_of_g(kord),
    }
  }

  fn canon_cmp_member_same_kind_ctx(x: KConstantInfo, y: KConstantInfo,
                                  ctx: List‹(Addr, G)›) -> (G, G) {
    match x {
      KConstantInfo.Defn(xn, xt, xv, _xs, _xh) =>
        match y {
          KConstantInfo.Defn(yn, yt, yv, _ys, _yh) =>
            canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xn, yn)),
              canon_sord_then(canon_cmp_kexpr_ctx(xt, yt, ctx),
                            canon_cmp_kexpr_ctx(xv, yv, ctx))),
          _ => canon_sord_eq_strong(),
        },
      -- (is_unsafe, lvls, params, indices, |ctors|, ty, ctors[*]) —
      -- mirror canonical_check.rs compare_kindc. The ctors tail is what
      -- separates same-shape mutual inductives.
      KConstantInfo.Induct(xn, xt, xp, xi, xc, xu, xba, xidx) =>
        match y {
          KConstantInfo.Induct(yn, yt, yp, yi, yc, yu, yba, yidx) =>
            canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xu, yu)),
              canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xn, yn)),
                canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xp, yp)),
                  canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xi, yi)),
                    canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xc, yc)),
                      canon_sord_then(canon_cmp_kexpr_ctx(xt, yt, ctx),
                        canon_cmp_ctor_range_ctx(xba, xidx, yba, yidx,
                                               xc, ctx, 0))))))),
          _ => canon_sord_eq_strong(),
        },
      KConstantInfo.Rec(xn, xt, xp, xi, xm, xmi, xrules, xk, _xu, _xba, _xr) =>
        match y {
          KConstantInfo.Rec(yn, yt, yp, yi, ym, ymi, yrules, yk, _yu, _yba, _yr) =>
            canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xn, yn)),
              canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xp, yp)),
                canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xi, yi)),
                  canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xm, ym)),
                    canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xmi, ymi)),
                      canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xk, yk)),
                        canon_sord_then(canon_cmp_kexpr_ctx(xt, yt, ctx),
                          canon_cmp_krec_rule_list_ctx(xrules, yrules, ctx)))))))),
          _ => canon_sord_eq_strong(),
        },
      _ => canon_sord_eq_strong(),
    }
  }

  -- Walk cidx 0..nc, resolving each ctor from both inductives via
  -- get_ci_cprj (mirror compare_kctor_idxs_ctx; |ctors| compared
  -- upstream so both ranges exhaust together).
  fn canon_cmp_ctor_range_ctx(xba: Addr, xidx: G, yba: Addr, yidx: G,
                            nc: G, ctx: List‹(Addr, G)›, c: G) -> (G, G) {
    match nc - c {
      0 => canon_sord_eq_strong(),
      _ =>
        let xc = load(get_ci_cprj(xba, xidx, c));
        let yc = load(get_ci_cprj(yba, yidx, c));
        canon_sord_then(canon_cmp_ctor_pair_ctx(xc, yc, ctx),
                      canon_cmp_ctor_range_ctx(xba, xidx, yba, yidx,
                                             nc, ctx, c + 1)),
    }
  }

  -- (lvls, cidx, params, fields, ty) — block/ind_idx/unsafe excluded
  -- (mirror compare_kctor).
  fn canon_cmp_ctor_pair_ctx(x: KConstantInfo, y: KConstantInfo,
                           ctx: List‹(Addr, G)›) -> (G, G) {
    match x {
      KConstantInfo.Ctor(xn, xt, _xb, _xi, xc, xp, xf, _xu) =>
        match y {
          KConstantInfo.Ctor(yn, yt, _yb, _yi, yc, yp, yf, _yu) =>
            canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xn, yn)),
              canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xc, yc)),
                canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xp, yp)),
                  canon_sord_then(canon_sord_of_g(canon_ord_cmp_g(xf, yf)),
                                canon_cmp_kexpr_ctx(xt, yt, ctx))))),
          _ => canon_sord_of_g(canon_ord_cmp_g(canon_kind_ord(x), canon_kind_ord(y))),
        },
      _ => canon_sord_of_g(canon_ord_cmp_g(canon_kind_ord(x), canon_kind_ord(y))),
    }
  }

  -- ==========================================================================
  -- Block-local addr synthesis. Member proj addrs come from
  -- build_recur_addrs; ctor CPrj addrs mirror the compile-emitted
  -- wrapper serialization (same scheme as projection_addr).
  -- ==========================================================================
  fn canon_cprj_addr(block: Addr, ind_idx: G, cidx: G) -> Addr {
    let info = ConstantInfo.CPrj(ConstructorProj.Mk(
      idx_to_u64(ind_idx), idx_to_u64(cidx), block));
    let proj_c = Constant.Mk(info,
                             store(ListNode.Nil),
                             store(ListNode.Nil),
                             store(ListNode.Nil));
    let bytes = put_constant(proj_c, store(ListNode.Nil));
    bytes_to_addr(bytes)
  }

  -- Member KCI at position, via its projection wrapper addr (memoized
  -- by get_ci).
  fn canon_member_ci(proj_addrs: List‹Addr›, pos: G) -> KConstantInfo {
    load(get_ci(list_lookup(proj_addrs, pos)))
  }

  fn canon_member_num_ctors(proj_addrs: List‹Addr›, pos: G) -> G {
    match canon_member_ci(proj_addrs, pos) {
      KConstantInfo.Induct(_, _, _, _, nc, _, _, _) => nc,
      _ => 0,
    }
  }

  -- ==========================================================================
  -- KMutCtx builder (mirror build_mut_ctx / KMutCtx::from_id_classes):
  -- class members map to class index j (all tied members share j → weak
  -- Equal), each Indc member's ctors map to i + cidx where i starts at
  -- |classes| and advances by each class's max ctor count.
  -- ==========================================================================
  fn canon_build_ctx(classes: List‹List‹G››, proj_addrs: List‹Addr›,
                   block: Addr) -> List‹(Addr, G)› {
    canon_build_ctx_classes(classes, proj_addrs, block, 0, list_length(classes))
  }

  fn canon_build_ctx_classes(classes: List‹List‹G››, proj_addrs: List‹Addr›,
                           block: Addr, j: G, i: G) -> List‹(Addr, G)› {
    match load(classes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(cls, rest) =>
        let (entries, max_ctors) =
          canon_build_ctx_members(cls, proj_addrs, block, j, i);
        list_concat(entries,
          canon_build_ctx_classes(rest, proj_addrs, block, j + 1, i + max_ctors)),
    }
  }

  fn canon_build_ctx_members(members: List‹G›, proj_addrs: List‹Addr›,
                           block: Addr, j: G, i: G)
                           -> (List‹(Addr, G)›, G) {
    match load(members) {
      ListNode.Nil => (store(ListNode.Nil), 0),
      ListNode.Cons(pos, rest) =>
        let (rest_entries, rest_max) =
          canon_build_ctx_members(rest, proj_addrs, block, j, i);
        let n = canon_member_num_ctors(proj_addrs, pos);
        let ctor_entries = canon_ctor_ctx_entries(block, pos, n, i, 0);
        let entries = store(ListNode.Cons(
          (list_lookup(proj_addrs, pos), j),
          list_concat(ctor_entries, rest_entries)));
        match u32_less_than(rest_max, n) {
          1 => (entries, n),
          _ => (entries, rest_max),
        },
    }
  }

  fn canon_ctor_ctx_entries(block: Addr, ind_idx: G, n: G, i: G,
                          cidx: G) -> List‹(Addr, G)› {
    match n - cidx {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons((canon_cprj_addr(block, ind_idx, cidx), i + cidx),
          canon_ctor_ctx_entries(block, ind_idx, n, i, cidx + 1))),
    }
  }

  -- ==========================================================================
  -- Iterative partition refinement (mirror sort_kconsts,
  -- canonical_check.rs:650-696). Fuel = 1 + |members| always reaches
  -- the fixpoint (each non-fixpoint round splits ≥1 class).
  -- ==========================================================================
  fn canon_sort_members(members: List‹G›, proj_addrs: List‹Addr›,
                      block: Addr) -> List‹List‹G›› {
    let seed = store(ListNode.Cons(members, store(ListNode.Nil)));
    canon_sort_loop(seed, proj_addrs, block, 1 + list_length(members))
  }

  fn canon_sort_loop(classes: List‹List‹G››, proj_addrs: List‹Addr›,
                   block: Addr, fuel: G) -> List‹List‹G›› {
    match fuel {
      0 => classes,
      _ =>
        let ctx = canon_build_ctx(classes, proj_addrs, block);
        let new_classes = canon_refine_classes(classes, ctx, proj_addrs);
        match canon_classes_eq(classes, new_classes) {
          1 => classes,
          _ => canon_sort_loop(new_classes, proj_addrs, block, fuel - 1),
        },
    }
  }

  fn canon_refine_classes(classes: List‹List‹G››, ctx: List‹(Addr, G)›,
                        proj_addrs: List‹Addr›) -> List‹List‹G›› {
    match load(classes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, rest) =>
        let refined = canon_refine_one(c, ctx, proj_addrs);
        list_concat(refined, canon_refine_classes(rest, ctx, proj_addrs)),
    }
  }

  fn canon_refine_one(c: List‹G›, ctx: List‹(Addr, G)›,
                    proj_addrs: List‹Addr›) -> List‹List‹G›› {
    match list_length(c) {
      0 => store(ListNode.Nil),
      1 => store(ListNode.Cons(c, store(ListNode.Nil))),
      _ =>
        let sorted = canon_ins_sort(c, ctx, proj_addrs);
        canon_group_consec(sorted, ctx, proj_addrs),
    }
  }

  fn canon_ins_sort(xs: List‹G›, ctx: List‹(Addr, G)›,
                  proj_addrs: List‹Addr›) -> List‹G› {
    match load(xs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(x, rest) =>
        canon_insert_sorted(x, canon_ins_sort(rest, ctx, proj_addrs),
                          ctx, proj_addrs),
    }
  }

  fn canon_insert_sorted(x: G, sorted: List‹G›, ctx: List‹(Addr, G)›,
                       proj_addrs: List‹Addr›) -> List‹G› {
    match load(sorted) {
      ListNode.Nil => store(ListNode.Cons(x, store(ListNode.Nil))),
      ListNode.Cons(h, rest) =>
        match canon_cmp_member_ctx(canon_member_ci(proj_addrs, x),
                                 canon_member_ci(proj_addrs, h), ctx) {
          (0, _) => store(ListNode.Cons(x, sorted)),
          _ => store(ListNode.Cons(h,
                 canon_insert_sorted(x, rest, ctx, proj_addrs))),
        },
    }
  }

  fn canon_group_consec(sorted: List‹G›, ctx: List‹(Addr, G)›,
                      proj_addrs: List‹Addr›) -> List‹List‹G›› {
    match load(sorted) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(h, rest) =>
        canon_group_walk(rest, ctx, proj_addrs, h,
                       store(ListNode.Cons(h, store(ListNode.Nil)))),
    }
  }

  fn canon_group_walk(remaining: List‹G›, ctx: List‹(Addr, G)›,
                    proj_addrs: List‹Addr›, last: G,
                    current: List‹G›) -> List‹List‹G›› {
    match load(remaining) {
      ListNode.Nil => store(ListNode.Cons(current, store(ListNode.Nil))),
      ListNode.Cons(h, rest) =>
        match canon_cmp_member_ctx(canon_member_ci(proj_addrs, last),
                                 canon_member_ci(proj_addrs, h), ctx) {
          (1, _) =>
            canon_group_walk(rest, ctx, proj_addrs, h, list_snoc(current, h)),
          _ =>
            store(ListNode.Cons(current,
              canon_group_walk(rest, ctx, proj_addrs, h,
                store(ListNode.Cons(h, store(ListNode.Nil)))))),
        },
    }
  }

  fn canon_classes_eq(a: List‹List‹G››, b: List‹List‹G››) -> G {
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
            match canon_g_list_eq(ah, bh) {
              0 => 0,
              _ => canon_classes_eq(arest, brest),
            },
        },
    }
  }

  fn canon_g_list_eq(xs: List‹G›, ys: List‹G›) -> G {
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
              0 => canon_g_list_eq(xt, yt),
              _ => 0,
            },
        },
    }
  }

  fn canon_flatten(classes: List‹List‹G››) -> List‹G› {
    match load(classes) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, rest) =>
        list_concat(c, canon_flatten(rest)),
    }
  }

  fn canon_all_singleton(classes: List‹List‹G››) -> G {
    match load(classes) {
      ListNode.Nil => 1,
      ListNode.Cons(c, rest) =>
        match list_length(c) {
          1 => canon_all_singleton(rest),
          _ => 0,
        },
    }
  }

  -- Indc member positions in the Muts list, ascending (mirror
  -- filter_indc_positions / Rust ingress.rs:2025-2048 — canonical
  -- order is validated for the Indc subset only).
  fn canon_indc_positions(members: List‹MutConst›, pos: G) -> List‹G› {
    match load(members) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        let tail = canon_indc_positions(rest, pos + 1);
        match m {
          MutConst.Indc(_) => store(ListNode.Cons(pos, tail)),
          _ => tail,
        },
    }
  }

  -- 1 iff `members` contains a member of the requested kind:
  -- `want_defn = 1` asks about Defn members, `want_defn = 0` about Indc.
  -- Recr members answer neither.
  fn canon_muts_has_kind(members: List‹MutConst›, want_defn: G) -> G {
    match load(members) {
      ListNode.Nil => 0,
      ListNode.Cons(m, rest) =>
        let hit = match m {
          MutConst.Defn(_) => want_defn,
          MutConst.Indc(_) => 1 - want_defn,
          MutConst.Recr(_) => 0,
        };
        match hit {
          1 => 1,
          _ => canon_muts_has_kind(rest, want_defn),
        },
    }
  }

  -- ==========================================================================
  -- Entry. Validate one Muts block's canonical member order (mirror
  -- validate_by_full_refinement): sort the Indc members by refinement,
  -- assert all classes are singletons (no alpha-collisions — Lean's
  -- compiler must have collapsed those) and the canonical sort equals
  -- the stored order. Aiur-memoized per block addr; non-Muts blocks
  -- and blocks with <2 Indc members pass trivially.
  -- ==========================================================================
  fn check_canonical_block(block_addr: Addr) {
    let c = load_verified_constant(block_addr);
    match c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            -- A block may not mix a definition member with inductive
            -- members. Lean emits neither: a `Declaration` is either
            -- `mutualDefnDecl` (all definitions) or `inductDecl`
            -- (inductives plus their recursors), and the auxiliaries an
            -- inductive generates are separate constants or themselves
            -- inductives.
            --
            -- This is what keeps strict positivity honest.
            -- `check_positivity_aug` skips a constructor field whose
            -- domain does not SYNTACTICALLY mention a block inductive,
            -- and `caddr_is_peer` counts a `Const` only when its info is
            -- an `Induct` — so a `Const` resolving to a definition scores
            -- zero and the domain is never reduced. The occurrence is
            -- therefore invisible whenever a definition stands between
            -- the field and the inductive.
            --
            -- Content addressing already rules that out everywhere else:
            -- for a definition `D` to mention this block's inductive, and
            -- for a constructor field to be `D`, each address would have
            -- to hash the other. The one way to have both without a cycle
            -- is for `D` to be a MEMBER, addressed off the block like the
            -- inductive is. Banning the mixture closes the class rather
            -- than the instance, and costs one pass per block instead of
            -- a reduction per field.
            assert_eq!(canon_muts_has_kind(members, 1) *
                         canon_muts_has_kind(members, 0), 0,
              "mutual block mixes a definition member with inductives");
            let indcs = canon_indc_positions(members, 0);
            match u32_less_than(list_length(indcs), 2) {
              1 => (),
              _ =>
                let proj_addrs = build_recur_addrs(members, block_addr);
                let classes = canon_sort_members(indcs, proj_addrs, block_addr);
                assert_eq!(canon_all_singleton(classes), 1,
                  "canonical block: refinement left members tied, order ambiguous");
                assert_eq!(canon_g_list_eq(canon_flatten(classes), indcs), 1,
                  "canonical block: members are not in canonical order");
                (),
            },
          _ => (),
        },
    }
  }
⟧

end IxVM

end
