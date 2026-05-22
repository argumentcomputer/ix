module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Level operations + literal equality + expr_inst_levels

Mirror: src/ix/kernel/level.rs + literal-equality helpers from
src/ix/kernel/expr.rs. Self-contained; new kernel modules
(Subst/Whnf/Infer/DefEq/Check) import from here.
-/

def levels := ⟦
  fn level_is_not_zero(l: KLevel) -> G {
    match l {
      KLevel.Zero => 0,
      KLevel.Param(_) => 0,
      KLevel.Succ(_) => 1,
      KLevel.Max(&a, &b) => match (level_is_not_zero(a), level_is_not_zero(b)) {
        (0, 0) => 0,
        _ => 1,
      },
      KLevel.IMax(_, &b) => level_is_not_zero(b),
    }
  }

  fn level_eq(a: KLevel, b: KLevel) -> G {
    match a {
      KLevel.Zero =>
        match b {
          KLevel.Zero => 1,
          _ => 0,
        },
      KLevel.Succ(&a1) =>
        match b {
          KLevel.Succ(&b1) => level_eq(a1, b1),
          _ => 0,
        },
      KLevel.Max(&a1, &a2) =>
        match b {
          KLevel.Max(&b1, &b2) => level_eq(a1, b1) * level_eq(a2, b2),
          _ => 0,
        },
      KLevel.IMax(&a1, &a2) =>
        match b {
          KLevel.IMax(&b1, &b2) => level_eq(a1, b1) * level_eq(a2, b2),
          _ => 0,
        },
      KLevel.Param(i) =>
        match b {
          KLevel.Param(j) => eq_zero(i - j),
          _ => 0,
        },
    }
  }

  fn level_has_param(l: KLevel) -> G {
    match l {
      KLevel.Zero => 0,
      KLevel.Param(_) => 1,
      KLevel.Succ(&a) => level_has_param(a),
      KLevel.Max(&a, &b) =>
        let ha = level_has_param(a);
        match ha {
          1 => 1,
          0 => level_has_param(b),
        },
      KLevel.IMax(&a, &b) =>
        let hb = level_has_param(b);
        match hb {
          1 => 1,
          0 => level_has_param(a),
        },
    }
  }

  fn level_any_param(l: KLevel) -> G {
    match l {
      KLevel.Param(i) => i,
      KLevel.Succ(&a) => level_any_param(a),
      KLevel.Max(&a, &b) =>
        let ha = level_has_param(a);
        match ha {
          1 => level_any_param(a),
          0 => level_any_param(b),
        },
      KLevel.IMax(&a, &b) =>
        let hb = level_has_param(b);
        match hb {
          1 => level_any_param(b),
          0 => level_any_param(a),
        },
      KLevel.Zero => 0,
    }
  }

  fn level_subst_reduce(l: KLevel, p: G, repl: KLevel) -> KLevel {
    match l {
      KLevel.Zero => KLevel.Zero,
      KLevel.Param(i) =>
        match i - p {
          0 => repl,
          _ => KLevel.Param(i),
        },
      KLevel.Succ(&a) =>
        KLevel.Succ(store(level_subst_reduce(a, p, repl))),
      KLevel.Max(&a, &b) =>
        level_max(level_subst_reduce(a, p, repl), level_subst_reduce(b, p, repl)),
      KLevel.IMax(&a, &b) =>
        level_imax(level_subst_reduce(a, p, repl), level_subst_reduce(b, p, repl)),
    }
  }

  fn level_leq(a: KLevel, b: KLevel) -> G {
    match a {
      KLevel.Zero => 1,
      KLevel.Max(&a1, &a2) =>
        level_leq(a1, b) * level_leq(a2, b),
      KLevel.Succ(&a1) =>
        match a1 {
          KLevel.Max(&x, &y) =>
            level_leq(KLevel.Succ(store(x)), b) * level_leq(KLevel.Succ(store(y)), b),
          _ =>
            match b {
              KLevel.Succ(&b1) => level_leq(a1, b1),
              KLevel.Max(&b1, &b2) =>
                let r1 = level_leq(a, b1);
                match r1 {
                  1 => 1,
                  0 =>
                    let r2 = level_leq(a, b2);
                    match r2 {
                      1 => 1,
                      0 =>
                        let bfull = KLevel.Max(store(b1), store(b2));
                        let hp = level_has_param(bfull);
                        match hp {
                          0 => 0,
                          _ =>
                            let p = level_any_param(bfull);
                            let sp = KLevel.Succ(store(KLevel.Param(p)));
                            let a0 = level_subst_reduce(a, p, KLevel.Zero);
                            let b0 = level_subst_reduce(bfull, p, KLevel.Zero);
                            let a1s = level_subst_reduce(a, p, sp);
                            let b1s = level_subst_reduce(bfull, p, sp);
                            level_leq(a0, b0) * level_leq(a1s, b1s),
                        },
                    },
                },
              _ => 0,
            },
        },
      KLevel.Param(i) =>
        match b {
          KLevel.Param(j) => eq_zero(i - j),
          KLevel.Succ(&b1) => level_leq(a, b1),
          KLevel.Max(&b1, &b2) =>
            let r1 = level_leq(a, b1);
            match r1 {
              1 => 1,
              0 => level_leq(a, b2),
            },
          KLevel.IMax(&b1, &b2) =>
            let p = level_any_param(b2);
            let sp = KLevel.Succ(store(KLevel.Param(p)));
            let a0 = level_subst_reduce(a, p, KLevel.Zero);
            let bfull = KLevel.IMax(store(b1), store(b2));
            let b0 = level_subst_reduce(bfull, p, KLevel.Zero);
            let a1s = level_subst_reduce(a, p, sp);
            let b1s = level_subst_reduce(bfull, p, sp);
            level_leq(a0, b0) * level_leq(a1s, b1s),
          KLevel.Zero => 0,
        },
      KLevel.IMax(&a1, &a2) =>
        let not_zero = level_is_not_zero(a2);
        match not_zero {
          1 => level_leq(a1, b) * level_leq(a2, b),
          0 =>
            let p = level_any_param(a2);
            let sp = KLevel.Succ(store(KLevel.Param(p)));
            let afull = KLevel.IMax(store(a1), store(a2));
            let a0 = level_subst_reduce(afull, p, KLevel.Zero);
            let b0 = level_subst_reduce(b, p, KLevel.Zero);
            let a1s = level_subst_reduce(afull, p, sp);
            let b1s = level_subst_reduce(b, p, sp);
            level_leq(a0, b0) * level_leq(a1s, b1s),
        },
    }
  }

  fn level_equal(a: KLevel, b: KLevel) -> G {
    level_leq(a, b) * level_leq(b, a)
  }

  fn level_max(a: KLevel, b: KLevel) -> KLevel {
    match a {
      KLevel.Zero => b,
      _ =>
        match b {
          KLevel.Zero => a,
          _ =>
            let eq = level_eq(a, b);
            match eq {
              1 => a,
              0 =>
                match a {
                  KLevel.Succ(&a1) =>
                    match b {
                      KLevel.Succ(&b1) => KLevel.Succ(store(level_max(a1, b1))),
                      _ => KLevel.Max(store(a), store(b)),
                    },
                  _ => KLevel.Max(store(a), store(b)),
                },
            },
        },
    }
  }

  fn level_imax(a: KLevel, b: KLevel) -> KLevel {
    match b {
      KLevel.Zero => KLevel.Zero,
      KLevel.Succ(_) => level_max(a, b),
      _ =>
        let not_zero = level_is_not_zero(b);
        match not_zero {
          1 => level_max(a, b),
          0 =>
            match a {
              KLevel.Zero => b,
              _ =>
                let eq = level_eq(a, b);
                match eq {
                  1 => a,
                  0 => KLevel.IMax(store(a), store(b)),
                },
            },
        },
    }
  }

  fn level_reduce(l: KLevel) -> KLevel {
    match l {
      KLevel.Zero => KLevel.Zero,
      KLevel.Param(i) => KLevel.Param(i),
      KLevel.Succ(&u) => KLevel.Succ(store(level_reduce(u))),
      KLevel.Max(&a, &b) => level_max(level_reduce(a), level_reduce(b)),
      KLevel.IMax(&a, &b) => level_imax(level_reduce(a), level_reduce(b)),
    }
  }

  fn level_inst_params(l: KLevel, params: List‹&KLevel›) -> KLevel {
    match l {
      KLevel.Zero => KLevel.Zero,
      KLevel.Succ(&u) => KLevel.Succ(store(level_inst_params(u, params))),
      KLevel.Max(&a, &b) =>
        level_max(level_inst_params(a, params), level_inst_params(b, params)),
      KLevel.IMax(&a, &b) =>
        level_imax(level_inst_params(a, params), level_inst_params(b, params)),
      KLevel.Param(i) => load(list_lookup(params, i)),
    }
  }

  fn level_list_inst(lvls: List‹&KLevel›, params: List‹&KLevel›) -> List‹&KLevel› {
    match load(lvls) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(&l, rest) =>
        store(ListNode.Cons(
          store(level_inst_params(l, params)),
          level_list_inst(rest, params))),
    }
  }

  fn expr_inst_levels(e: KExpr, params: List‹&KLevel›) -> KExpr {
    -- Fast path: empty param list = identity. Common when caller's lvls
    -- list is Nil (constants with no universe params).
    match load(params) {
      ListNode.Nil => e,
      _ => expr_inst_levels_walk(e, params),
    }
  }

  fn expr_inst_levels_walk(e: KExpr, params: List‹&KLevel›) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) => store(KExprNode.BVar(i)),
      KExprNode.Srt(&l) =>
        store(KExprNode.Srt(store(level_inst_params(l, params)))),
      KExprNode.Const(idx, lvls) =>
        store(KExprNode.Const(idx, level_list_inst(lvls, params))),
      KExprNode.App(f, a) =>
        store(KExprNode.App(expr_inst_levels(f, params), expr_inst_levels(a, params))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(expr_inst_levels(ty, params), expr_inst_levels(body, params))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(expr_inst_levels(ty, params), expr_inst_levels(body, params))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          expr_inst_levels(ty, params),
          expr_inst_levels(val, params),
          expr_inst_levels(body, params))),
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, expr_inst_levels(e1, params))),
    }
  }

  -- ============================================================================
  -- Literal equality
  -- ============================================================================

  fn klimbs_eq(a: KLimbs, b: KLimbs) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(lb, rb) =>
            let eq = u64_eq(la, lb);
            match eq {
              1 => klimbs_eq(ra, rb),
              0 => 0,
            },
        },
    }
  }

  fn bytestream_eq(a: ByteStream, b: ByteStream) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(ba, ra) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(bb, rb) =>
            match to_field(ba) - to_field(bb) {
              0 => bytestream_eq(ra, rb),
              _ => 0,
            },
        },
    }
  }

  fn literal_eq(a: KLiteral, b: KLiteral) -> G {
    match a {
      KLiteral.Nat(na) =>
        match b {
          KLiteral.Nat(nb) => klimbs_eq(na, nb),
          _ => 0,
        },
      KLiteral.Str(sa) =>
        match b {
          KLiteral.Str(sb) => bytestream_eq(sa, sb),
          _ => 0,
        },
    }
  }
⟧

end IxVM

end
