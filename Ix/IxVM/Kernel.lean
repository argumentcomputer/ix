module
public import Ix.Aiur.Meta

public section

namespace IxVM

def kernel := ⟦
  -- ============================================================================
  -- List operations
  -- ============================================================================

  -- Look up a value in a value environment by de Bruijn index
  fn val_env_lookup(env: KValEnv, idx: [G; 8]) -> KVal {
    match env {
      KValEnv.Cons(&v, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => v,
          0 => val_env_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  -- Look up a value in a value list by index
  fn val_list_lookup(list: KValList, idx: [G; 8]) -> KVal {
    match list {
      KValList.Cons(&v, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => v,
          0 => val_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  -- Append a value to the end of a list
  fn val_list_snoc(list: KValList, v: KVal) -> KValList {
    match list {
      KValList.Nil => KValList.Cons(store(v), store(KValList.Nil)),
      KValList.Cons(&head, &rest) =>
        KValList.Cons(store(head), store(val_list_snoc(rest, v))),
    }
  }

  -- Compute the length of a value list
  fn val_list_length(list: KValList) -> [G; 8] {
    match list {
      KValList.Nil => [0; 8],
      KValList.Cons(_, &rest) => relaxed_u64_succ(val_list_length(rest)),
    }
  }

  -- Look up a level in a level list by index
  fn level_list_lookup(list: KLevelList, idx: [G; 8]) -> KLevel {
    match list {
      KLevelList.Cons(&l, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => l,
          0 => level_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  -- Look up a constant info in a constant list by index
  fn const_list_lookup(list: KConstList, idx: [G; 8]) -> KConstantInfo {
    match list {
      KConstList.Cons(&ci, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => ci,
          0 => const_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  -- Find recursor rule by constructor index
  fn rec_rule_find(rules: KRecRuleList, ctor_idx: [G; 8]) -> KRecRule {
    match rules {
      KRecRuleList.Cons(&rule, &rest) =>
        match rule {
          KRecRule.Mk(idx, nf, &rhs) =>
            let found = u64_eq(idx, ctor_idx);
            match found {
              1 => KRecRule.Mk(idx, nf, store(rhs)),
              0 => rec_rule_find(rest, ctor_idx),
            },
        },
    }
  }

  -- Extract the ctor_idx from the first rule in a KRecRuleList
  fn rec_rule_first_ctor(rules: KRecRuleList) -> [G; 8] {
    match rules {
      KRecRuleList.Cons(&rule, _) =>
        match rule {
          KRecRule.Mk(ctor_idx, _, _) => ctor_idx,
        },
    }
  }

  -- Extract the first element from a KU64List (for single-constructor inductives)
  fn ku64_list_head(list: KU64List) -> [G; 8] {
    match list {
      KU64List.Cons(v, _) => v,
    }
  }

  -- Extract the second element from a KU64List
  fn ku64_list_second(list: KU64List) -> [G; 8] {
    match list {
      KU64List.Cons(_, &rest) =>
        match rest {
          KU64List.Cons(v, _) => v,
        },
    }
  }

  -- ============================================================================
  -- Constant info accessors
  -- ============================================================================

  -- Extract the type expression from any constant info variant
  fn const_type(ci: KConstantInfo) -> KExpr {
    match ci {
      KConstantInfo.Axiom(_, &ty, _) => ty,
      KConstantInfo.Defn(_, &ty, _, _, _) => ty,
      KConstantInfo.Thm(_, &ty, _) => ty,
      KConstantInfo.Opaque(_, &ty, _, _) => ty,
      KConstantInfo.Quot(_, &ty, _) => ty,
      KConstantInfo.Induct(_, &ty, _, _, _, _, _, _) => ty,
      KConstantInfo.Ctor(_, &ty, _, _, _, _, _) => ty,
      KConstantInfo.Rec(_, &ty, _, _, _, _, _, _, _) => ty,
    }
  }

  -- Extract the number of universe level parameters from any constant info variant
  fn const_num_levels(ci: KConstantInfo) -> [G; 8] {
    match ci {
      KConstantInfo.Axiom(n, _, _) => n,
      KConstantInfo.Defn(n, _, _, _, _) => n,
      KConstantInfo.Thm(n, _, _) => n,
      KConstantInfo.Opaque(n, _, _, _) => n,
      KConstantInfo.Quot(n, _, _) => n,
      KConstantInfo.Induct(n, _, _, _, _, _, _, _) => n,
      KConstantInfo.Ctor(n, _, _, _, _, _, _) => n,
      KConstantInfo.Rec(n, _, _, _, _, _, _, _, _) => n,
    }
  }

  -- ============================================================================
  -- Level operations
  -- ============================================================================

  -- Check if a level is definitely not zero (sound approximation)
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

  -- Structural equality of levels (after reduction)
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
          KLevel.Param(j) => u64_eq(i, j),
          _ => 0,
        },
    }
  }

  -- level_leq: check a <= b (heuristic, sound but incomplete)
  fn level_leq(a: KLevel, b: KLevel) -> G {
    match a {
      KLevel.Zero => 1,
      -- max(a1, a2) <= b iff a1 <= b and a2 <= b
      KLevel.Max(&a1, &a2) =>
        level_leq(a1, b) * level_leq(a2, b),
      KLevel.Succ(&a1) =>
        match b {
          KLevel.Succ(&b1) => level_leq(a1, b1),
          KLevel.Max(&b1, &b2) =>
            let r1 = level_leq(a, b1);
            match r1 {
              1 => 1,
              0 => level_leq(a, b2),
            },
          _ => 0,
        },
      KLevel.Param(i) =>
        match b {
          KLevel.Param(j) => u64_eq(i, j),
          KLevel.Max(&b1, &b2) =>
            let r1 = level_leq(a, b1);
            match r1 {
              1 => 1,
              0 => level_leq(a, b2),
            },
          _ => 0,
        },
      KLevel.IMax(&a1, &a2) =>
        match b {
          KLevel.Max(&b1, &b2) =>
            let r1 = level_leq(a, b1);
            match r1 {
              1 => 1,
              0 => level_leq(a, b2),
            },
          _ => level_eq(a, b),
        },
    }
  }

  -- Semantic level equality: a <= b AND b <= a
  fn level_equal(a: KLevel, b: KLevel) -> G {
    level_leq(a, b) * level_leq(b, a)
  }

  -- Reduce max(a, b) assuming a and b are already reduced
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

  -- Reduce imax(a, b) assuming a and b are already reduced
  fn level_imax(a: KLevel, b: KLevel) -> KLevel {
    match b {
      KLevel.Zero => KLevel.Zero,
      KLevel.Succ(_) => level_max(a, b),
      _ =>
        match a {
          KLevel.Zero => b,
          _ =>
            let eq = level_eq(a, b);
            match eq {
              1 => a,
              0 => KLevel.IMax(store(a), store(b)),
            },
        },
    }
  }

  -- Reduce a level to normal form
  fn level_reduce(l: KLevel) -> KLevel {
    match l {
      KLevel.Zero => KLevel.Zero,
      KLevel.Param(i) => KLevel.Param(i),
      KLevel.Succ(&u) => KLevel.Succ(store(level_reduce(u))),
      KLevel.Max(&a, &b) => level_max(level_reduce(a), level_reduce(b)),
      KLevel.IMax(&a, &b) => level_imax(level_reduce(a), level_reduce(b)),
    }
  }

  -- Substitute all Level.Param(i) -> params[i] in a level
  fn level_inst_params(l: KLevel, params: KLevelList) -> KLevel {
    match l {
      KLevel.Zero => KLevel.Zero,
      KLevel.Succ(&u) => KLevel.Succ(store(level_inst_params(u, params))),
      KLevel.Max(&a, &b) =>
        level_max(level_inst_params(a, params), level_inst_params(b, params)),
      KLevel.IMax(&a, &b) =>
        level_imax(level_inst_params(a, params), level_inst_params(b, params)),
      KLevel.Param(i) => level_list_lookup(params, i),
    }
  }

  -- ============================================================================
  -- Expression-level level substitution
  -- ============================================================================

  -- Substitute all Level.Param(i) -> params[i] in all levels within an expression
  fn expr_inst_levels(e: KExpr, params: KLevelList) -> KExpr {
    match e {
      KExpr.BVar(i) => KExpr.BVar(i),
      KExpr.Srt(&l) =>
        KExpr.Srt(store(level_inst_params(l, params))),
      KExpr.Const(idx, &lvls) =>
        KExpr.Const(idx, store(level_list_inst(lvls, params))),
      KExpr.App(&f, &a) =>
        KExpr.App(store(expr_inst_levels(f, params)), store(expr_inst_levels(a, params))),
      KExpr.Lam(&ty, &body) =>
        KExpr.Lam(store(expr_inst_levels(ty, params)), store(expr_inst_levels(body, params))),
      KExpr.Forall(&ty, &body) =>
        KExpr.Forall(store(expr_inst_levels(ty, params)), store(expr_inst_levels(body, params))),
      KExpr.Let(&ty, &val, &body) =>
        KExpr.Let(
          store(expr_inst_levels(ty, params)),
          store(expr_inst_levels(val, params)),
          store(expr_inst_levels(body, params))),
      KExpr.Lit(lit) => KExpr.Lit(lit),
      KExpr.Proj(tidx, fidx, &e1) =>
        KExpr.Proj(tidx, fidx, store(expr_inst_levels(e1, params))),
    }
  }

  -- Substitute level params in a level list
  fn level_list_inst(lvls: KLevelList, params: KLevelList) -> KLevelList {
    match lvls {
      KLevelList.Nil => KLevelList.Nil,
      KLevelList.Cons(&l, &rest) =>
        KLevelList.Cons(
          store(level_inst_params(l, params)),
          store(level_list_inst(rest, params))),
    }
  }

  -- ============================================================================
  -- Evaluation (NbE)
  -- ============================================================================

  -- Evaluate an expression to a value using Normalization by Evaluation (NbE)
  fn k_eval(e: KExpr, env: KValEnv, top: KConstList) -> KVal {
    match e {
      KExpr.BVar(idx) =>
        val_env_lookup(env, idx),

      KExpr.Srt(&l) =>
        KVal.Srt(store(level_reduce(l))),

      KExpr.Const(idx, &lvls) =>
        k_eval_const(idx, lvls, top),

      KExpr.App(&f, &a) =>
        let vf = k_eval(f, env, top);
        let va = k_eval(a, env, top);
        k_apply(vf, va, top),

      KExpr.Lam(&ty, &body) =>
        let ty_val = k_eval(ty, env, top);
        KVal.Lam(store(ty_val), store(body), store(env)),

      KExpr.Forall(&ty, &body) =>
        let ty_val = k_eval(ty, env, top);
        KVal.Pi(store(ty_val), store(body), store(env)),

      KExpr.Let(_, &val, &body) =>
        let v = k_eval(val, env, top);
        let env2 = KValEnv.Cons(store(v), store(env));
        k_eval(body, env2, top),

      KExpr.Lit(lit) =>
        KVal.Lit(lit),

      KExpr.Proj(tidx, fidx, &e1) =>
        let v = k_eval(e1, env, top);
        k_eval_proj(tidx, fidx, v),
    }
  }

  -- Evaluate a constant reference
  fn k_eval_const(idx: [G; 8], lvls: KLevelList, top: KConstList) -> KVal {
    let ci = const_list_lookup(top, idx);
    match ci {
      KConstantInfo.Defn(_, _, &value, hints, _) =>
        match hints {
          KHints.Opaque =>
            KVal.Const(idx, store(lvls), store(KValList.Nil)),
          KHints.Abbrev =>
            let body = expr_inst_levels(value, lvls);
            k_eval(body, KValEnv.Nil, top),
          KHints.Regular(_) =>
            let body = expr_inst_levels(value, lvls);
            k_eval(body, KValEnv.Nil, top),
        },

      KConstantInfo.Ctor(_, _, _, _, nparams, _, _) =>
        KVal.Ctor(idx, store(lvls), nparams, store(KValList.Nil)),

      -- Theorems, opaques, axioms, recursors, inductives, quotients: irreducible
      _ => KVal.Const(idx, store(lvls), store(KValList.Nil)),
    }
  }

  -- Evaluate a projection
  fn k_eval_proj(tidx: [G; 8], fidx: [G; 8], v: KVal) -> KVal {
    match v {
      KVal.Ctor(_, _, nparams, &spine) =>
        let field_idx = u64_add(nparams, fidx);
        val_list_lookup(spine, field_idx),
      _ =>
        KVal.Proj(tidx, fidx, store(v), store(KValList.Nil)),
    }
  }

  -- Apply a value to an argument
  fn k_apply(f: KVal, arg: KVal, top: KConstList) -> KVal {
    match f {
      KVal.Lam(_, &body, &env) =>
        let env2 = KValEnv.Cons(store(arg), store(env));
        k_eval(body, env2, top),

      KVal.Ctor(idx, &lvls, nparams, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        KVal.Ctor(idx, store(lvls), nparams, store(spine2)),

      KVal.FVar(lvl, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        KVal.FVar(lvl, store(spine2)),

      KVal.Const(idx, &lvls, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        try_iota(idx, lvls, spine2, top),

      KVal.Proj(tidx, fidx, &sv, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        KVal.Proj(tidx, fidx, store(sv), store(spine2)),
    }
  }

  -- Apply a value to a list of arguments
  fn k_apply_spine(f: KVal, spine: KValList, top: KConstList) -> KVal {
    match spine {
      KValList.Nil => f,
      KValList.Cons(&v, &rest) =>
        let f2 = k_apply(f, v, top);
        k_apply_spine(f2, rest, top),
    }
  }

  -- ============================================================================
  -- Iota reduction (recursor on constructor)
  -- ============================================================================

  -- Get induct_idx from a constructor's constant info
  fn ctor_induct_idx(ctor_idx: [G; 8], top: KConstList) -> [G; 8] {
    let ctor_ci = const_list_lookup(top, ctor_idx);
    match ctor_ci {
      KConstantInfo.Ctor(_, _, induct_idx, _, _, _, _) => induct_idx,
    }
  }

  -- Try iota reduction: if idx refers to a recursor and the major premise is a
  -- constructor or Nat literal, apply the matching recursor rule; otherwise return a neutral VConst
  fn try_iota(idx: [G; 8], lvls: KLevelList, spine: KValList, top: KConstList) -> KVal {
    let ci = const_list_lookup(top, idx);
    match ci {
      KConstantInfo.Rec(_, _, nparams, nindices, nmotives, nminors, &rules, _, _) =>
        let maj_idx = u64_add(u64_add(u64_add(nparams, nmotives), nminors), nindices);
        let spine_len = val_list_length(spine);
        let not_have_major = u64_is_zero(u64_sub(relaxed_u64_succ(spine_len), relaxed_u64_succ(maj_idx)));
        match not_have_major {
          1 => KVal.Const(idx, store(lvls), store(spine)),
          0 =>
            let major_raw = val_list_lookup(spine, maj_idx);
            let major = k_whnf(major_raw, top);
            match major {
              KVal.Ctor(ctor_idx, _, ctor_nparams, &ctor_spine) =>
                let rule = rec_rule_find(rules, ctor_idx);
                match rule {
                  KRecRule.Mk(_, nfields, &rhs) =>
                    let rhs_inst = expr_inst_levels(rhs, lvls);
                    let rhs_val = k_eval(rhs_inst, KValEnv.Nil, top);
                    let params_motives_minors = val_list_take(spine, u64_add(u64_add(nparams, nmotives), nminors));
                    let result = k_apply_spine(rhs_val, params_motives_minors, top);
                    let fields = val_list_drop(ctor_spine, ctor_nparams);
                    let result2 = k_apply_spine(result, fields, top);
                    let remaining = val_list_drop(spine, relaxed_u64_succ(maj_idx));
                    k_apply_spine(result2, remaining, top),
                },
              KVal.Lit(lit) =>
                match lit {
                  KLiteral.Nat(n) =>
                    -- Nat literal iota: Lit(0) → zero rule, Lit(n+1) → succ rule with Lit(n)
                    -- Derive the inductive idx from the first rule's ctor_idx
                    let first_ctor_idx = rec_rule_first_ctor(rules);
                    let induct_idx = ctor_induct_idx(first_ctor_idx, top);
                    let ind_ci = const_list_lookup(top, induct_idx);
                    match ind_ci {
                      KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
                        let pmm_end = u64_add(u64_add(nparams, nmotives), nminors);
                        let is_zero = u64_is_zero(n);
                        match is_zero {
                          1 =>
                            -- Lit(0) → fire zero rule with no ctor fields
                            let zero_ctor_idx = ku64_list_head(ctor_indices);
                            let rule = rec_rule_find(rules, zero_ctor_idx);
                            match rule {
                              KRecRule.Mk(_, _, &rhs) =>
                                let rhs_inst = expr_inst_levels(rhs, lvls);
                                let rhs_val = k_eval(rhs_inst, KValEnv.Nil, top);
                                let pmm = val_list_take(spine, pmm_end);
                                let result = k_apply_spine(rhs_val, pmm, top);
                                let remaining = val_list_drop(spine, relaxed_u64_succ(maj_idx));
                                k_apply_spine(result, remaining, top),
                            },
                          0 =>
                            -- Lit(n+1) → fire succ rule with one field = Lit(n-1)
                            let succ_ctor_idx = ku64_list_second(ctor_indices);
                            let rule = rec_rule_find(rules, succ_ctor_idx);
                            match rule {
                              KRecRule.Mk(_, _, &rhs) =>
                                let rhs_inst = expr_inst_levels(rhs, lvls);
                                let rhs_val = k_eval(rhs_inst, KValEnv.Nil, top);
                                let pmm = val_list_take(spine, pmm_end);
                                let result = k_apply_spine(rhs_val, pmm, top);
                                let pred = KVal.Lit(KLiteral.Nat(relaxed_u64_pred(n)));
                                let ctor_fields = KValList.Cons(store(pred), store(KValList.Nil));
                                let result2 = k_apply_spine(result, ctor_fields, top);
                                let remaining = val_list_drop(spine, relaxed_u64_succ(maj_idx));
                                k_apply_spine(result2, remaining, top),
                            },
                        },
                    },
                  KLiteral.Str(_) =>
                    KVal.Const(idx, store(lvls), store(spine)),
                },
              _ =>
                KVal.Const(idx, store(lvls), store(spine)),
            },
        },

      _ => KVal.Const(idx, store(lvls), store(spine)),
    }
  }

  -- Take the first n elements of a val list
  fn val_list_take(list: KValList, n: [G; 8]) -> KValList {
    let z = u64_is_zero(n);
    match z {
      1 => KValList.Nil,
      0 =>
        match list {
          KValList.Cons(&v, &rest) =>
            KValList.Cons(store(v), store(val_list_take(rest, relaxed_u64_pred(n)))),
        },
    }
  }

  -- Drop the first n elements of a val list
  fn val_list_drop(list: KValList, n: [G; 8]) -> KValList {
    let z = u64_is_zero(n);
    match z {
      1 => list,
      0 =>
        match list {
          KValList.Cons(_, &rest) =>
            val_list_drop(rest, relaxed_u64_pred(n)),
        },
    }
  }

  -- ============================================================================
  -- WHNF (additional reductions beyond eval)
  -- ============================================================================

  -- Reduce a value to Weak Head Normal Form by retrying projection, iota, and delta reductions


  fn k_whnf(v: KVal, top: KConstList) -> KVal {
    match v {
      KVal.Proj(tidx, fidx, &sv, &spine) =>
        let sv2 = k_whnf(sv, top);
        match sv2 {
          KVal.Ctor(_, _, nparams, &ctor_spine) =>
            let field_idx = u64_add(nparams, fidx);
            let field = val_list_lookup(ctor_spine, field_idx);
            let result = k_apply_spine(field, spine, top);
            k_whnf(result, top),
          KVal.Const(cidx, _, &cspine) =>
            KVal.Proj(tidx, fidx, store(sv2), store(spine)),
          _ =>
            KVal.Proj(tidx, fidx, store(sv2), store(spine)),
        },

      KVal.Const(idx, &lvls, &spine) =>
        -- First try iota reduction (recursor on constructor)
        let result = try_iota(idx, lvls, spine, top);
        match result {
          KVal.Const(idx2, &lvls2, &spine2) =>
            let same = u64_eq(idx, idx2);
            match same {
              0 => k_whnf(result, top),
              1 =>
                -- Iota didn't fire; try delta unfolding
                let ci = const_list_lookup(top, idx2);
                match ci {
                  KConstantInfo.Defn(_, _, &value, hints, _) =>
                    match hints {
                      KHints.Opaque => result,
                      _ =>
                        let body = expr_inst_levels(value, lvls2);
                        let val = k_eval(body, KValEnv.Nil, top);
                        let val2 = k_apply_spine(val, spine2, top);
                        k_whnf(val2, top),
                    },
                  -- Theorems are opaque (not unfolded)
                  _ => result,
                },
            },
          _ => k_whnf(result, top),
        },

      _ => v,
    }
  }

  -- ============================================================================
  -- Quotation (values back to expressions)
  -- ============================================================================

  -- Quote a value back into an expression (readback), converting free variables
  -- to de Bruijn indices relative to the current depth
  fn k_quote(v: KVal, depth: [G; 8], top: KConstList) -> KExpr {
    match v {
      KVal.Srt(&l) => KExpr.Srt(store(l)),

      KVal.Lit(lit) => KExpr.Lit(lit),

      KVal.Lam(&dom, &body, &env) =>
        let dom_expr = k_quote(dom, depth, top);
        let fvar = KVal.FVar(depth, store(KValList.Nil));
        let env2 = KValEnv.Cons(store(fvar), store(env));
        let body_val = k_eval(body, env2, top);
        let body_expr = k_quote(body_val, relaxed_u64_succ(depth), top);
        KExpr.Lam(store(dom_expr), store(body_expr)),

      KVal.Pi(&dom, &body, &env) =>
        let dom_expr = k_quote(dom, depth, top);
        let fvar = KVal.FVar(depth, store(KValList.Nil));
        let env2 = KValEnv.Cons(store(fvar), store(env));
        let body_val = k_eval(body, env2, top);
        let body_expr = k_quote(body_val, relaxed_u64_succ(depth), top);
        KExpr.Forall(store(dom_expr), store(body_expr)),

      KVal.Ctor(idx, &lvls, _, &spine) =>
        let base = KExpr.Const(idx, store(lvls));
        quote_spine(base, spine, depth, top),

      KVal.FVar(lvl, &spine) =>
        let idx = u64_sub(relaxed_u64_pred(depth), lvl);
        let base = KExpr.BVar(idx);
        quote_spine(base, spine, depth, top),

      KVal.Const(idx, &lvls, &spine) =>
        let base = KExpr.Const(idx, store(lvls));
        quote_spine(base, spine, depth, top),

      KVal.Proj(tidx, fidx, &sv, &spine) =>
        let sv_expr = k_quote(sv, depth, top);
        let base = KExpr.Proj(tidx, fidx, store(sv_expr));
        quote_spine(base, spine, depth, top),
    }
  }

  -- Quote a spine of arguments, wrapping each in an EApp around the base expression
  fn quote_spine(base: KExpr, spine: KValList, depth: [G; 8], top: KConstList) -> KExpr {
    match spine {
      KValList.Nil => base,
      KValList.Cons(&v, &rest) =>
        let arg_expr = k_quote(v, depth, top);
        let app = KExpr.App(store(base), store(arg_expr));
        quote_spine(app, rest, depth, top),
    }
  }

  -- ============================================================================
  -- Projection type inference helpers
  -- ============================================================================

  -- ============================================================================
  -- Type inference
  -- ============================================================================

  -- Infer the type of an expression under the given type and value environments.
  -- nat_idx/str_idx are the constant indices for the Nat/String types (for literal typing).
  fn k_infer(e: KExpr, types: KValList, env: KValEnv, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> KVal {
    match e {
      KExpr.BVar(idx) =>
        val_list_lookup(types, idx),

      KExpr.Srt(&l) =>
        KVal.Srt(store(KLevel.Succ(store(l)))),

      KExpr.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) =>
            KVal.Const(nat_idx, store(KLevelList.Nil), store(KValList.Nil)),
          KLiteral.Str(_) =>
            KVal.Const(str_idx, store(KLevelList.Nil), store(KValList.Nil)),
        },

      KExpr.Const(idx, &lvls) =>
        let ci = const_list_lookup(top, idx);
        let expected = const_num_levels(ci);
        let given = level_list_length(lvls);
        let lvl_eq = u64_eq(expected, given);
        assert_eq!(lvl_eq, 1);
        let ty = const_type(ci);
        let ty_inst = expr_inst_levels(ty, lvls);
        k_eval(ty_inst, KValEnv.Nil, top),

      KExpr.App(&f, &a) =>
        let fn_type = k_infer(f, types, env, depth, top, nat_idx, str_idx);
        let fn_type_whnf = k_whnf(fn_type, top);
        match fn_type_whnf {
          KVal.Pi(&dom, &body, &pi_env) =>
            let arg_type = k_infer(a, types, env, depth, top, nat_idx, str_idx);
            let app_eq = k_is_def_eq(arg_type, dom, depth, top, nat_idx, str_idx);
            assert_eq!(app_eq, 1);
            let arg_val = k_eval(a, env, top);
            let pi_env2 = KValEnv.Cons(store(arg_val), store(pi_env));
            k_eval(body, pi_env2, top),
        },

      KExpr.Lam(&ty, &body) =>
        let _x = k_ensure_sort(ty, types, env, depth, top, nat_idx, str_idx);
        let dom_val = k_eval(ty, env, top);
        let fvar = KVal.FVar(depth, store(KValList.Nil));
        let types2 = KValList.Cons(store(dom_val), store(types));
        let env2 = KValEnv.Cons(store(fvar), store(env));
        let body_type = k_infer(body, types2, env2, relaxed_u64_succ(depth), top, nat_idx, str_idx);
        let body_type_expr = k_quote(body_type, relaxed_u64_succ(depth), top);
        KVal.Pi(store(dom_val), store(body_type_expr), store(env)),

      KExpr.Forall(&ty, &body) =>
        let dom_level = k_ensure_sort(ty, types, env, depth, top, nat_idx, str_idx);
        let dom_val = k_eval(ty, env, top);
        let fvar = KVal.FVar(depth, store(KValList.Nil));
        let types2 = KValList.Cons(store(dom_val), store(types));
        let env2 = KValEnv.Cons(store(fvar), store(env));
        let body_level = k_ensure_sort(body, types2, env2, relaxed_u64_succ(depth), top, nat_idx, str_idx);
        let result_level = level_imax(dom_level, body_level);
        KVal.Srt(store(result_level)),

      KExpr.Let(&ty, &val, &body) =>
        let _x = k_ensure_sort(ty, types, env, depth, top, nat_idx, str_idx);
        let ty_val = k_eval(ty, env, top);
        let val_type = k_infer(val, types, env, depth, top, nat_idx, str_idx);
        let let_eq = k_is_def_eq(val_type, ty_val, depth, top, nat_idx, str_idx);
        assert_eq!(let_eq, 1);
        let val_val = k_eval(val, env, top);
        let types2 = KValList.Cons(store(ty_val), store(types));
        let env2 = KValEnv.Cons(store(val_val), store(env));
        k_infer(body, types2, env2, relaxed_u64_succ(depth), top, nat_idx, str_idx),

      KExpr.Proj(tidx, fidx, &e1) =>
        -- Infer struct type and WHNF to expose inductive head
        let struct_type = k_infer(e1, types, env, depth, top, nat_idx, str_idx);
        let struct_type_whnf = k_whnf(struct_type, top);
        match struct_type_whnf {
          KVal.Const(induct_idx, &levels, &params_spine) =>
            -- Look up inductive to get its single constructor index
            let ind_ci = const_list_lookup(top, induct_idx);
            match ind_ci {
              KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
                let ctor_idx = ku64_list_head(ctor_indices);
                -- Get the constructor type, instantiate levels, and eval
                let ctor_ci = const_list_lookup(top, ctor_idx);
                let ctor_type_expr = const_type(ctor_ci);
                let ctor_type_inst = expr_inst_levels(ctor_type_expr, levels);
                let ctor_type_val = k_eval(ctor_type_inst, KValEnv.Nil, top);
                -- Walk past params using values from the inductive's spine
                let after_params = walk_params(ctor_type_val, params_spine, top);
                -- Walk past preceding fields using Proj values
                let struct_val = k_eval(e1, env, top);
                let after_fields = walk_fields(after_params, tidx, [0; 8], fidx, struct_val, top);
                -- Extract the domain type at field fidx
                let result_whnf = k_whnf(after_fields, top);
                match result_whnf {
                  KVal.Pi(&dom, _, _) => dom,
                },
            },
        },
    }
  }

  -- Ensure a type expression evaluates to a Sort, returning the level
  fn k_ensure_sort(e: KExpr, types: KValList, env: KValEnv, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> KLevel {
    let ty = k_infer(e, types, env, depth, top, nat_idx, str_idx);
    let ty_whnf = k_whnf(ty, top);
    match ty_whnf {
      KVal.Srt(&l) => l,
    }
  }

  -- Compute the length of a level list
  fn level_list_length(list: KLevelList) -> [G; 8] {
    match list {
      KLevelList.Nil => [0; 8],
      KLevelList.Cons(_, &rest) => relaxed_u64_succ(level_list_length(rest)),
    }
  }

  -- Walk past n Pi binders, substituting param values from the spine
  fn walk_params(ct: KVal, params: KValList, top: KConstList) -> KVal {
    match params {
      KValList.Nil => ct,
      KValList.Cons(&param_val, &rest_params) =>
        let ct_whnf = k_whnf(ct, top);
        match ct_whnf {
          KVal.Pi(_, &body, &pi_env) =>
            let env2 = KValEnv.Cons(store(param_val), store(pi_env));
            let next = k_eval(body, env2, top);
            walk_params(next, rest_params, top),
        },
    }
  }

  -- Walk past n fields in a constructor type, substituting Proj values
  fn walk_fields(ct: KVal, tidx: [G; 8], current_field: [G; 8], remaining: [G; 8], struct_val: KVal, top: KConstList) -> KVal {
    let z = u64_is_zero(remaining);
    match z {
      1 => ct,
      0 =>
        let ct_whnf = k_whnf(ct, top);
        match ct_whnf {
          KVal.Pi(_, &body, &pi_env) =>
            let proj_val = KVal.Proj(tidx, current_field, store(struct_val), store(KValList.Nil));
            let env2 = KValEnv.Cons(store(proj_val), store(pi_env));
            let next = k_eval(body, env2, top);
            walk_fields(next, tidx, relaxed_u64_succ(current_field), relaxed_u64_pred(remaining), struct_val, top),
        },
    }
  }

  -- ============================================================================
  -- Debug helpers
  -- ============================================================================

  -- ============================================================================
  -- Proof irrelevance helpers
  -- ============================================================================

  -- Apply a spine of argument values to a type by walking through Pi-bindings
  fn apply_spine_to_type(ty: KVal, spine: KValList, top: KConstList) -> KVal {
    match spine {
      KValList.Nil => ty,
      KValList.Cons(&arg, &rest) =>
        let ty_whnf = k_whnf(ty, top);
        match ty_whnf {
          KVal.Pi(_, &body, &pi_env) =>
            let env2 = KValEnv.Cons(store(arg), store(pi_env));
            let next = k_eval(body, env2, top);
            apply_spine_to_type(next, rest, top),
          -- If not a Pi, we're stuck; return as-is (sentinel)
          _ => ty_whnf,
        },
    }
  }

  -- Infer the type of a value (best-effort, no error handling).
  -- Returns Sort 1 as sentinel for cases we can't handle (FVar, Lam, Proj).
  fn k_infer_val_type(v: KVal, top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> KVal {
    match v {
      KVal.Srt(&l) => KVal.Srt(store(KLevel.Succ(store(l)))),
      KVal.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) => KVal.Const(nat_idx, store(KLevelList.Nil), store(KValList.Nil)),
          KLiteral.Str(_) => KVal.Const(str_idx, store(KLevelList.Nil), store(KValList.Nil)),
        },
      KVal.Const(idx, &lvls, &spine) =>
        let ci = const_list_lookup(top, idx);
        let ty = const_type(ci);
        let ty_inst = expr_inst_levels(ty, lvls);
        let ty_val = k_eval(ty_inst, KValEnv.Nil, top);
        apply_spine_to_type(ty_val, spine, top),
      KVal.Ctor(idx, &lvls, _, &spine) =>
        let ci = const_list_lookup(top, idx);
        let ty = const_type(ci);
        let ty_inst = expr_inst_levels(ty, lvls);
        let ty_val = k_eval(ty_inst, KValEnv.Nil, top);
        apply_spine_to_type(ty_val, spine, top),
      KVal.Proj(tidx, fidx, &sv, &spine) =>
        let struct_type = k_infer_val_type(sv, top, nat_idx, str_idx);
        let struct_type_whnf = k_whnf(struct_type, top);
        match struct_type_whnf {
          KVal.Const(induct_idx, &levels, &params_spine) =>
            let ind_ci = const_list_lookup(top, induct_idx);
            match ind_ci {
              KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
                let ctor_idx = ku64_list_head(ctor_indices);
                let ctor_ci = const_list_lookup(top, ctor_idx);
                let ctor_type_expr = const_type(ctor_ci);
                let ctor_type_inst = expr_inst_levels(ctor_type_expr, levels);
                let ctor_type_val = k_eval(ctor_type_inst, KValEnv.Nil, top);
                let after_params = walk_params(ctor_type_val, params_spine, top);
                let after_fields = walk_fields(after_params, tidx, [0; 8], fidx, sv, top);
                let result_whnf = k_whnf(after_fields, top);
                match result_whnf {
                  KVal.Pi(&dom, _, _) => apply_spine_to_type(dom, spine, top),
                  -- If not a Pi, return the type itself (could be the final result type)
                  _ => apply_spine_to_type(result_whnf, spine, top),
                },
              -- Not an inductive, fall back to sentinel
              _ => KVal.Srt(store(KLevel.Succ(store(KLevel.Zero)))),
            },
          -- If struct type can't be determined, fall back to sentinel
          _ => KVal.Srt(store(KLevel.Succ(store(KLevel.Zero)))),
        },
      -- For FVar, Lam, Pi: return Sort 1 as sentinel (never Prop)
      _ => KVal.Srt(store(KLevel.Succ(store(KLevel.Zero)))),
    }
  }

  -- Check if a value is a proposition (its type is Sort 0 / Prop)
  fn k_is_prop_val(v: KVal, top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    let ty = k_infer_val_type(v, top, nat_idx, str_idx);
    let ty_whnf = k_whnf(ty, top);
    match ty_whnf {
      KVal.Srt(&l) =>
        match l {
          KLevel.Zero => 1,
          _ => 0,
        },
      _ => 0,
    }
  }

  -- ============================================================================
  -- Struct eta helpers
  -- ============================================================================

  -- Get num_fields from a constructor's constant info
  fn ctor_num_fields(ctor_idx: [G; 8], top: KConstList) -> [G; 8] {
    let ctor_ci = const_list_lookup(top, ctor_idx);
    match ctor_ci {
      KConstantInfo.Ctor(_, _, _, _, _, nfields, _) => nfields,
    }
  }

  -- Check if a constructor belongs to a struct-like type (exactly 1 constructor)
  fn is_struct_like(ctor_idx: [G; 8], top: KConstList) -> G {
    let ctor_ci = const_list_lookup(top, ctor_idx);
    match ctor_ci {
      KConstantInfo.Ctor(_, _, induct_idx, _, _, nfields, _) =>
        let ind_ci = const_list_lookup(top, induct_idx);
        match ind_ci {
          KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
            let num_ctors = ku64_list_length(ctor_indices);
            let one = relaxed_u64_succ([0; 8]);
            u64_eq(num_ctors, one),
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Compare each field: Proj(tidx, i, t) vs spine[nparams + i]
  fn eta_struct_fields(t: KVal, spine: KValList, nparams: [G; 8], tidx: [G; 8], current: [G; 8], remaining: [G; 8], depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    let z = u64_is_zero(remaining);
    match z {
      1 => 1,
      0 =>
        let field_idx = u64_add(nparams, current);
        let field_val = val_list_lookup(spine, field_idx);
        let proj_val = KVal.Proj(tidx, current, store(t), store(KValList.Nil));
        let eq = k_is_def_eq(proj_val, field_val, depth, top, nat_idx, str_idx);
        match eq {
          0 => 0,
          1 => eta_struct_fields(t, spine, nparams, tidx, relaxed_u64_succ(current), relaxed_u64_pred(remaining), depth, top, nat_idx, str_idx),
        },
    }
  }

  -- Try struct eta: if s is a Ctor of a struct-like type, compare fields
  fn try_eta_struct_one(t: KVal, s: KVal, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    match s {
      KVal.Ctor(ctor_idx, _, nparams, &spine) =>
        let struct_like = is_struct_like(ctor_idx, top);
        match struct_like {
          0 => 0,
          1 =>
            let induct_idx = ctor_induct_idx(ctor_idx, top);
            let num_fields = ctor_num_fields(ctor_idx, top);
            eta_struct_fields(t, spine, nparams, induct_idx, [0; 8], num_fields, depth, top, nat_idx, str_idx),
        },
      _ => 0,
    }
  }

  -- Try struct eta in both directions
  fn try_eta_struct(a: KVal, b: KVal, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    let r1 = try_eta_struct_one(a, b, depth, top, nat_idx, str_idx);
    match r1 {
      1 => 1,
      0 => try_eta_struct_one(b, a, depth, top, nat_idx, str_idx),
    }
  }

  -- ============================================================================
  -- Definitional equality
  -- ============================================================================

  -- Check definitional equality of two values: first try a quick syntactic check,
  -- then reduce to WHNF and compare structurally
  fn k_is_def_eq(a: KVal, b: KVal, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    let quick = k_quick_def_eq(a, b);
    match quick {
      1 => 1,
      0 =>
        let a_whnf = k_whnf(a, top);
        let b_whnf = k_whnf(b, top);
        let quick2 = k_quick_def_eq(a_whnf, b_whnf);
        match quick2 {
          1 => 1,
          0 =>
            -- Proof irrelevance: if both are proofs (types in Prop), compare types
            let a_type = k_infer_val_type(a_whnf, top, nat_idx, str_idx);
            let a_is_prop = k_is_prop_val(a_type, top, nat_idx, str_idx);
            match a_is_prop {
              1 =>
                let b_type = k_infer_val_type(b_whnf, top, nat_idx, str_idx);
                let b_is_prop = k_is_prop_val(b_type, top, nat_idx, str_idx);
                match b_is_prop {
                  1 =>
                    k_is_def_eq(a_type, b_type, depth, top, nat_idx, str_idx),
                  0 =>
                    let core_res = k_is_def_eq_core(a_whnf, b_whnf, depth, top, nat_idx, str_idx);
                    match core_res {
                      0 =>
                        let eta_res = try_eta_struct(a_whnf, b_whnf, depth, top, nat_idx, str_idx);
                        match eta_res {
                          1 => 1,
                          0 =>
                            0,
                        },
                      1 => 1,
                    },
                },
              0 =>
                let core_res = k_is_def_eq_core(a_whnf, b_whnf, depth, top, nat_idx, str_idx);
                match core_res {
                  0 =>
                    let eta_res = try_eta_struct(a_whnf, b_whnf, depth, top, nat_idx, str_idx);
                    match eta_res {
                      1 => 1,
                      0 =>
                        0,
                    },
                  1 => 1,
                },
            },
        },
    }
  }

  -- Quick syntactic check for definitional equality (sorts and literals only)
  fn k_quick_def_eq(a: KVal, b: KVal) -> G {
    match a {
      KVal.Srt(&la) =>
        match b {
          KVal.Srt(&lb) => level_equal(la, lb),
          _ => 0,
        },
      KVal.Lit(la) =>
        match b {
          KVal.Lit(lb) => literal_eq(la, lb),
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Check equality of two literals (nat or string, compared by their u64 values)
  fn literal_eq(a: KLiteral, b: KLiteral) -> G {
    match a {
      KLiteral.Nat(na) =>
        match b {
          KLiteral.Nat(nb) => u64_eq(na, nb),
          _ => 0,
        },
      KLiteral.Str(sa) =>
        match b {
          KLiteral.Str(sb) => u64_eq(sa, sb),
          _ => 0,
        },
    }
  }

  -- Compare a Nat literal with a Nat constructor value
  -- Lit(0) == Ctor(zero_ctor, _, nparams, spine) when spine.len == nparams (no fields)
  -- Lit(n+1) == Ctor(succ_ctor, _, nparams, spine) when spine.len == nparams + 1
  --   and Lit(n) == spine[nparams]
  fn nat_lit_eq_ctor(
    lit: KLiteral, ctor_idx: [G; 8], nparams: [G; 8], ctor_spine: KValList,
    depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]
  ) -> G {
    match lit {
      KLiteral.Nat(n) =>
        let induct_idx = ctor_induct_idx(ctor_idx, top);
        let is_nat = u64_eq(induct_idx, nat_idx);
        match is_nat {
          0 => 0,
          1 =>
            let nfields = ctor_num_fields(ctor_idx, top);
            let is_zero = u64_is_zero(n);
            match is_zero {
              1 =>
                -- Lit(0) == Ctor if ctor has 0 fields
                u64_is_zero(nfields),
              0 =>
                -- Lit(n+1) == Ctor if ctor has 1 field and that field == Lit(n)
                let has_one = u64_eq(nfields, [1, 0, 0, 0, 0, 0, 0, 0]);
                match has_one {
                  0 => 0,
                  1 =>
                    let pred_val = val_list_lookup(ctor_spine, nparams);
                    let pred_lit = KVal.Lit(KLiteral.Nat(relaxed_u64_pred(n)));
                    k_is_def_eq(pred_lit, pred_val, depth, top, nat_idx, str_idx),
                },
            },
        },
      KLiteral.Str(_) => 0,
    }
  }

  -- Structural definitional equality after WHNF
  fn k_is_def_eq_core(a: KVal, b: KVal, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    match a {
      KVal.Srt(&la) =>
        match b {
          KVal.Srt(&lb) => level_equal(la, lb),
          _ => 0,
        },

      KVal.Lit(la) =>
        match b {
          KVal.Lit(lb) => literal_eq(la, lb),
          KVal.Ctor(ctor_idx, _, nparams, &ctor_spine) =>
            nat_lit_eq_ctor(la, ctor_idx, nparams, ctor_spine, depth, top, nat_idx, str_idx),
          _ => 0,
        },

      KVal.FVar(lvl_a, &sp_a) =>
        match b {
          KVal.FVar(lvl_b, &sp_b) =>
            let same_lvl = u64_eq(lvl_a, lvl_b);
            match same_lvl {
              1 => k_is_def_eq_spine(sp_a, sp_b, depth, top, nat_idx, str_idx),
              0 => 0,
            },
          _ => 0,
        },

      KVal.Const(idx_a, &lvls_a, &sp_a) =>
        match b {
          KVal.Const(idx_b, &lvls_b, &sp_b) =>
            let same_idx = u64_eq(idx_a, idx_b);
            match same_idx {
              1 =>
                let lvls_eq = k_is_def_eq_levels(lvls_a, lvls_b);
                match lvls_eq {
                  1 => k_is_def_eq_spine(sp_a, sp_b, depth, top, nat_idx, str_idx),
                  0 => 0,
                },
              0 =>
                k_lazy_delta(a, b, depth, top, nat_idx, str_idx),
            },
          _ => k_lazy_delta(a, b, depth, top, nat_idx, str_idx),
        },

      KVal.Ctor(idx_a, &lvls_a, nparams_a, &sp_a) =>
        match b {
          KVal.Ctor(idx_b, &lvls_b, _, &sp_b) =>
            let same_idx = u64_eq(idx_a, idx_b);
            match same_idx {
              1 =>
                let lvls_eq = k_is_def_eq_levels(lvls_a, lvls_b);
                match lvls_eq {
                  1 => k_is_def_eq_spine(sp_a, sp_b, depth, top, nat_idx, str_idx),
                  0 => 0,
                },
              0 => 0,
            },
          KVal.Lit(lb) =>
            nat_lit_eq_ctor(lb, idx_a, nparams_a, sp_a, depth, top, nat_idx, str_idx),
          _ => 0,
        },

      KVal.Lam(&dom_a, &body_a, &env_a) =>
        match b {
          KVal.Lam(&dom_b, &body_b, &env_b) =>
            let dom_eq = k_is_def_eq(dom_a, dom_b, depth, top, nat_idx, str_idx);
            match dom_eq {
              0 => 0,
              1 =>
                let fvar = KVal.FVar(depth, store(KValList.Nil));
                let env_a2 = KValEnv.Cons(store(fvar), store(env_a));
                let env_b2 = KValEnv.Cons(store(fvar), store(env_b));
                let va = k_eval(body_a, env_a2, top);
                let vb = k_eval(body_b, env_b2, top);
                k_is_def_eq(va, vb, relaxed_u64_succ(depth), top, nat_idx, str_idx),
            },
          _ =>
            -- Eta: lam vs non-lam
            let fvar = KVal.FVar(depth, store(KValList.Nil));
            let env_a2 = KValEnv.Cons(store(fvar), store(env_a));
            let va = k_eval(body_a, env_a2, top);
            let vb = k_apply(b, fvar, top);
            k_is_def_eq(va, vb, relaxed_u64_succ(depth), top, nat_idx, str_idx),
        },

      KVal.Pi(&dom_a, &body_a, &env_a) =>
        match b {
          KVal.Pi(&dom_b, &body_b, &env_b) =>
            let dom_eq = k_is_def_eq(dom_a, dom_b, depth, top, nat_idx, str_idx);
            match dom_eq {
              0 => 0,
              1 =>
                let fvar = KVal.FVar(depth, store(KValList.Nil));
                let env_a2 = KValEnv.Cons(store(fvar), store(env_a));
                let env_b2 = KValEnv.Cons(store(fvar), store(env_b));
                let va = k_eval(body_a, env_a2, top);
                let vb = k_eval(body_b, env_b2, top);
                k_is_def_eq(va, vb, relaxed_u64_succ(depth), top, nat_idx, str_idx),
            },
          _ => 0,
        },

      KVal.Proj(tidx_a, fidx_a, &sv_a, &sp_a) =>
        match b {
          KVal.Proj(tidx_b, fidx_b, &sv_b, &sp_b) =>
            let same_tf = u64_eq(tidx_a, tidx_b) * u64_eq(fidx_a, fidx_b);
            match same_tf {
              1 =>
                let sv_eq = k_is_def_eq(sv_a, sv_b, depth, top, nat_idx, str_idx);
                match sv_eq {
                  1 => k_is_def_eq_spine(sp_a, sp_b, depth, top, nat_idx, str_idx),
                  0 => 0,
                },
              0 => 0,
            },
          _ => 0,
        },

      -- Eta: non-lam vs lam (symmetric case)
      _ =>
        match b {
          KVal.Lam(&dom_b, &body_b, &env_b) =>
            let fvar = KVal.FVar(depth, store(KValList.Nil));
            let va = k_apply(a, fvar, top);
            let env_b2 = KValEnv.Cons(store(fvar), store(env_b));
            let vb = k_eval(body_b, env_b2, top);
            k_is_def_eq(va, vb, relaxed_u64_succ(depth), top, nat_idx, str_idx),
          KVal.Const(_, _, _) =>
            k_lazy_delta(a, b, depth, top, nat_idx, str_idx),
          _ => 0,
        },
    }
  }

  -- Pointwise definitional equality of two value spines
  fn k_is_def_eq_spine(a: KValList, b: KValList, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    match a {
      KValList.Nil =>
        match b {
          KValList.Nil => 1,
          _ => 0,
        },
      KValList.Cons(&va, &ra) =>
        match b {
          KValList.Nil => 0,
          KValList.Cons(&vb, &rb) =>
            let eq = k_is_def_eq(va, vb, depth, top, nat_idx, str_idx);
            match eq {
              0 => 0,
              1 => k_is_def_eq_spine(ra, rb, depth, top, nat_idx, str_idx),
            },
        },
    }
  }

  -- Pointwise semantic equality of two level lists
  fn k_is_def_eq_levels(a: KLevelList, b: KLevelList) -> G {
    match a {
      KLevelList.Nil =>
        match b {
          KLevelList.Nil => 1,
          _ => 0,
        },
      KLevelList.Cons(&la, &ra) =>
        match b {
          KLevelList.Nil => 0,
          KLevelList.Cons(&lb, &rb) =>
            let eq = level_equal(la, lb);
            match eq {
              0 => 0,
              1 => k_is_def_eq_levels(ra, rb),
            },
        },
    }
  }

  -- Lazy delta: try unfolding one or both constants to make progress
  fn k_lazy_delta(a: KVal, b: KVal, depth: [G; 8], top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    let a_unfolded = try_delta_unfold(a, top);
    let b_unfolded = try_delta_unfold(b, top);
    let a_changed = delta_changed(a, a_unfolded);
    let b_changed = delta_changed(b, b_unfolded);
    match (a_changed, b_changed) {
      (0, 0) => 0,
      _ => k_is_def_eq(a_unfolded, b_unfolded, depth, top, nat_idx, str_idx),
    }
  }

  -- Try to delta-unfold a VConst value by looking up its definition and evaluating it;
  -- returns the original value if it is opaque or not a definition
  fn try_delta_unfold(v: KVal, top: KConstList) -> KVal {
    match v {
      KVal.Const(idx, &lvls, &spine) =>
        let ci = const_list_lookup(top, idx);
        match ci {
          KConstantInfo.Defn(_, _, &value, hints, _) =>
            match hints {
              KHints.Opaque => v,
              KHints.Abbrev =>
                let body = expr_inst_levels(value, lvls);
                let val = k_eval(body, KValEnv.Nil, top);
                k_apply_spine(val, spine, top),
              KHints.Regular(_) =>
                let body = expr_inst_levels(value, lvls);
                let val = k_eval(body, KValEnv.Nil, top);
                k_apply_spine(val, spine, top),
            },
          _ => v,
        },
      _ => v,
    }
  }

  -- Check whether delta unfolding made progress (i.e., the head constant changed)
  fn delta_changed(before: KVal, after: KVal) -> G {
    match before {
      KVal.Const(idx_a, _, _) =>
        match after {
          KVal.Const(idx_b, _, _) => 1 - u64_eq(idx_a, idx_b),
          _ => 1,
        },
      _ => 0,
    }
  }

  -- ============================================================================
  -- Declaration checking
  -- ============================================================================

  -- Type-check a single constant declaration against the environment.
  -- nat_idx/str_idx are the constant indices for the Nat/String types.
  fn k_check_const(ci: KConstantInfo, top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    match ci {
      KConstantInfo.Axiom(_, &ty, _) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        1,

      KConstantInfo.Defn(_, &ty, &value, _, _) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        let ty_val = k_eval(ty, KValEnv.Nil, top);
        let val_type = k_infer(value, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        let eq = k_is_def_eq(val_type, ty_val, [0; 8], top, nat_idx, str_idx);
        assert_eq!(eq, 1);
        1,

      KConstantInfo.Thm(_, &ty, &value) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        let ty_val = k_eval(ty, KValEnv.Nil, top);
        let val_type = k_infer(value, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        let eq = k_is_def_eq(val_type, ty_val, [0; 8], top, nat_idx, str_idx);
        assert_eq!(eq, 1);
        1,

      KConstantInfo.Opaque(_, &ty, &value, _) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        let ty_val = k_eval(ty, KValEnv.Nil, top);
        let val_type = k_infer(value, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        let eq = k_is_def_eq(val_type, ty_val, [0; 8], top, nat_idx, str_idx);
        assert_eq!(eq, 1);
        1,

      KConstantInfo.Quot(_, &ty, _) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        1,

      KConstantInfo.Induct(_, &ty, _, _, _, _, _, _) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        1,

      KConstantInfo.Ctor(_, &ty, _, _, _, _, _) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        1,

      KConstantInfo.Rec(_, &ty, _, _, _, _, _, _, _) =>
        let _x = k_ensure_sort(ty, KValList.Nil, KValEnv.Nil, [0; 8], top, nat_idx, str_idx);
        1,
    }
  }

  fn k_check_all_go(consts: KConstList, top: KConstList, nat_idx: [G; 8], str_idx: [G; 8], idx: [G; 8]) -> G {
    match consts {
      KConstList.Nil => 1,
      KConstList.Cons(&ci, &rest) =>
        let _x = k_check_const(ci, top, nat_idx, str_idx);
        k_check_all_go(rest, top, nat_idx, str_idx, relaxed_u64_succ(idx)),
    }
  }

  fn k_check_all(consts: KConstList, top: KConstList, nat_idx: [G; 8], str_idx: [G; 8]) -> G {
    k_check_all_go(consts, top, nat_idx, str_idx, [0; 8])
  }

  -- ============================================================================
  -- Primitive type discovery
  -- ============================================================================

  -- Count the number of entries in a KU64List
  fn ku64_list_length(list: KU64List) -> [G; 8] {
    match list {
      KU64List.Nil => [0; 8],
      KU64List.Cons(_, &rest) => relaxed_u64_succ(ku64_list_length(rest)),
    }
  }

  -- Check if a constant at the given index is the Nat type:
  -- an Inductive with 0 params, 0 indices, 2 constructors where
  -- ctor[0] has 0 fields and ctor[1] has 1 field.
  fn is_nat_inductive(ci: KConstantInfo, top: KConstList, ctor_indices: KU64List) -> G {
    match ci {
      KConstantInfo.Induct(_, _, nparams, nindices, _, _, _, _) =>
        let params_zero = u64_is_zero(nparams);
        let indices_zero = u64_is_zero(nindices);
        let two_ctors = u64_eq(ku64_list_length(ctor_indices), [2, 0, 0, 0, 0, 0, 0, 0]);
        match params_zero * indices_zero * two_ctors {
          0 => 0,
          _ =>
            -- Check ctor[0] has 0 fields and ctor[1] has 1 field
            match ctor_indices {
              KU64List.Cons(ctor0_idx, &rest) =>
                match rest {
                  KU64List.Cons(ctor1_idx, _) =>
                    let ctor0 = const_list_lookup(top, ctor0_idx);
                    let ctor1 = const_list_lookup(top, ctor1_idx);
                    match ctor0 {
                      KConstantInfo.Ctor(_, _, _, _, _, nfields0, _) =>
                        match ctor1 {
                          KConstantInfo.Ctor(_, _, _, _, _, nfields1, _) =>
                            u64_is_zero(nfields0) * u64_eq(nfields1, [1, 0, 0, 0, 0, 0, 0, 0]),
                          _ => 0,
                        },
                      _ => 0,
                    },
                },
            },
        },
      _ => 0,
    }
  }

  -- Find the index of the Nat inductive in the constant list.
  -- Returns the index, or [255, 255, 255, 255, 255, 255, 255, 255] if not found.
  fn find_nat_idx(consts: KConstList, top: KConstList, idx: [G; 8]) -> [G; 8] {
    match consts {
      KConstList.Nil => [255, 255, 255, 255, 255, 255, 255, 255],
      KConstList.Cons(&ci, &rest) =>
        match ci {
          KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
            let found = is_nat_inductive(ci, top, ctor_indices);
            match found {
              1 => idx,
              0 => find_nat_idx(rest, top, relaxed_u64_succ(idx)),
            },
          _ => find_nat_idx(rest, top, relaxed_u64_succ(idx)),
        },
    }
  }
⟧

end IxVM

end
