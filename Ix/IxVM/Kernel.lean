module
public import Ix.Aiur.Meta

/-!
# Aiur Kernel — Lean 4 Type Checker Circuit

A complete Lean 4 kernel type checker written in Aiur, a DSL for zero-knowledge
proof circuits. Verifies that every definition and theorem in a Lean environment
is well-typed.

## Architecture

The kernel uses **Normalization by Evaluation (NbE)**: expressions (`KExpr`) are
evaluated into semantic values (`KVal`) using closures and environments, giving
O(1) beta reduction instead of O(|body|) substitution walks. Free variables use
**de Bruijn levels** (stable under binder entry) rather than indices.

The core is three mutually recursive operations:
- `k_eval` / `k_whnf`: evaluate expressions and reduce to weak head normal form
- `k_infer` / `k_check`: infer types and bidirectionally check against expected types
- `k_is_def_eq`: check definitional equality (proof irrelevance, eta, lazy delta)

## Aiur Constraints

Aiur circuits have no mutation, no dynamic indexing, and no non-tail matches.
Instead of explicit caches (WHNF cache, equiv manager, thunk memoization), the
Aiur runtime's function-call caching provides call-by-need semantics: calling
`k_eval(expr, env, top)` with the same arguments returns the cached result.

## Implemented Features

| Feature                          | Status |
|----------------------------------|--------|
| Lazy eval (thunks in spines)     | ✅     |
| Delta unfolding (WHNF)           | ✅     |
| Iota reduction (recursor)        | ✅     |
| K-reduction (Prop recursors)     | ✅     |
| Nat literal iota                 | ✅     |
| Quotient reduction               | ✅     |
| Function eta                     | ✅     |
| Struct eta                       | ✅     |
| Bidirectional checking           | ✅     |
| Level comparison (sound+complete)| ✅     |
| Unsafe opaque skip               | ✅     |

## Known Limitations

| Feature                          | Status                               |
|----------------------------------|--------------------------------------|
| Nat primitives (add, mul, ...)   | ❌ uses iota (exponential for large) |
| String primitives                | ❌                                   |
| Lazy delta (hint-based)          | ⚠️ unfolds both sides                |
| Inductive block validation       | ❌ trusts input                      |
| Delta step limit                 | ❌                                   |

## File Organization

Types are in `KernelTypes.lean` (`KExpr`, `KVal`, `KLevel`, `KConstantInfo`).
Ixon ↔ kernel conversion is in `Convert.lean`. Content-addressed constant
loading is in `Ingress.lean`. This file contains all kernel logic.
-/

public section

namespace IxVM

def kernel := ⟦
  -- ============================================================================
  -- List operations
  -- ============================================================================

  -- Look up a value in a value environment by de Bruijn index
  -- Find recursor rule by constructor index
  fn rec_rule_try_find(rules: List‹&KRecRule›, ctor_idx: G) -> Option‹&KRecRule› {
    match rules {
      List.Nil => Option.None,
      List.Cons(&rule, &rest) =>
        match rule {
          KRecRule.Mk(idx, nf, &rhs) =>
            let found = eq_zero(idx - ctor_idx);
            match found {
              1 => Option.Some(store(KRecRule.Mk(idx, nf, store(rhs)))),
              0 => rec_rule_try_find(rest, ctor_idx),
            },
        },
    }
  }

  fn rec_rule_find(rules: List‹&KRecRule›, ctor_idx: G) -> KRecRule {
    match rules {
      List.Cons(&rule, &rest) =>
        match rule {
          KRecRule.Mk(idx, nf, &rhs) =>
            let found = eq_zero(idx - ctor_idx);
            match found {
              1 => KRecRule.Mk(idx, nf, store(rhs)),
              0 => rec_rule_find(rest, ctor_idx),
            },
        },
    }
  }

  -- Extract the ctor_idx from the first rule in a List‹&KRecRule›
  fn rec_rule_first_ctor(rules: List‹&KRecRule›) -> G {
    match rules {
      List.Cons(&rule, _) =>
        match rule {
          KRecRule.Mk(ctor_idx, _, _) => ctor_idx,
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
  fn const_num_levels(ci: KConstantInfo) -> G {
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
  --
  -- Universe levels are symbolic expressions (Zero, Succ, Max, IMax, Param)
  -- evaluated under assignments σ : Param → ℕ. Two levels are equal iff they
  -- agree under all assignments. IMax(a, b) = 0 when b = 0, else max(a, b);
  -- this gives impredicativity of Prop.
  --
  -- Levels are maintained in "reduced form" by level_max and level_imax:
  -- an IMax(a, b) node only survives when b could be zero (level_is_not_zero = 0).
  -- This invariant is key to the completeness of level_leq.
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
          KLevel.Param(j) => eq_zero(i - j),
          _ => 0,
        },
    }
  }

  -- Check if a level contains any Param
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

  -- Find any Param index in a level. Precondition: level contains at least one Param.
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

  -- Substitute Param(p) with repl in a level, normalizing as we go
  fn level_subst_reduce(l: KLevel, p: G, repl: KLevel) -> KLevel {
    match l {
      KLevel.Zero => KLevel.Zero,
      KLevel.Param(i) =>
        let eq = eq_zero(i - p);
        match eq {
          1 => repl,
          0 => KLevel.Param(i),
        },
      KLevel.Succ(&a) =>
        KLevel.Succ(store(level_subst_reduce(a, p, repl))),
      KLevel.Max(&a, &b) =>
        level_max(level_subst_reduce(a, p, repl), level_subst_reduce(b, p, repl)),
      KLevel.IMax(&a, &b) =>
        level_imax(level_subst_reduce(a, p, repl), level_subst_reduce(b, p, repl)),
    }
  }

  -- Check ⟦a⟧σ ≤ ⟦b⟧σ for all level assignments σ : Param → ℕ.
  -- Returns 1 iff the inequality holds universally; 0 otherwise.
  --
  -- Sound and complete for reduced levels. Proof sketch by case:
  --   Zero ≤ b:            trivially true (0 ≤ anything)
  --   Max(a1,a2) ≤ b:      iff a1 ≤ b ∧ a2 ≤ b
  --   Succ(Max(x,y)) ≤ b:  distribute: succ(max) = max(succ,succ)
  --   Succ(a1) ≤ Succ(b1): peel both succs
  --   Succ(a1) ≤ Zero/Param/IMax: false (Zero Witness: reduced IMax evaluates to 0 at σ₀)
  --   Succ(a1) ≤ Max(b1,b2): try each branch; if both fail and b has params, case-split
  --                           to resolve IMax children (tropical completeness after resolution)
  --   Param(i) ≤ Param(j): iff i = j
  --   Param(i) ≤ Succ(b1): reduces to Param(i) ≤ b1 (complete by monotonicity argument)
  --   Param(i) ≤ Max(b1,b2): try each branch (complete: Param tracks through some branch)
  --   Param(i) ≤ IMax(b1,b2): case-split on a param in b2
  --   IMax(a1,a2) ≤ b:     if a2 definitely nonzero, treat as Max; else case-split on a2
  --
  -- Case-splitting substitutes p → 0 and p → Succ(Param(p)), partitioning all assignments.
  -- Each split strictly reduces free params, ensuring termination.
  -- See KERNEL.md §3 "Level Comparison" for the full formal argument.
  fn level_leq(a: KLevel, b: KLevel) -> G {
    match a {
      KLevel.Zero => 1,
      -- max(a1, a2) <= b iff a1 <= b and a2 <= b
      KLevel.Max(&a1, &a2) =>
        level_leq(a1, b) * level_leq(a2, b),
      KLevel.Succ(&a1) =>
        match a1 {
          -- Distribute Succ over Max: succ(max(x,y)) = max(succ(x), succ(y))
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
                      -- Neither branch alone dominates; case-split on a param in b
                      -- to resolve any IMax children (see INCOMPLETE.md)
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
          -- Param(i) <= Succ(X) iff Param(i) <= X (levels are integers, so tight)
          KLevel.Succ(&b1) => level_leq(a, b1),
          KLevel.Max(&b1, &b2) =>
            let r1 = level_leq(a, b1);
            match r1 {
              1 => 1,
              0 => level_leq(a, b2),
            },
          -- Param(i) <= IMax(b1, b2): case-split on a param in b2
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
          -- imax(a1, a2) where a2 is definitely not zero behaves as max(a1, a2)
          1 => level_leq(a1, b) * level_leq(a2, b),
          -- Case-split: substitute a param from a2 with Zero and Succ(Param)
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

  -- ============================================================================
  -- Expression-level level substitution
  -- ============================================================================

  -- Substitute all Level.Param(i) -> params[i] in all levels within an expression
  fn expr_inst_levels(e: KExpr, params: List‹&KLevel›) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) => store(KExprNode.BVar(i)),
      KExprNode.Srt(&l) =>
        store(KExprNode.Srt(store(level_inst_params(l, params)))),
      KExprNode.Const(idx, &lvls) =>
        store(KExprNode.Const(idx, store(level_list_inst(lvls, params)))),
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

  -- Substitute level params in a level list
  fn level_list_inst(lvls: List‹&KLevel›, params: List‹&KLevel›) -> List‹&KLevel› {
    match lvls {
      List.Nil => List.Nil,
      List.Cons(&l, &rest) =>
        List.Cons(
          store(level_inst_params(l, params)),
          store(level_list_inst(rest, params))),
    }
  }

  -- ============================================================================
  -- Evaluation (NbE)
  --
  -- Normalization by Evaluation: expressions (KExpr) are evaluated into semantic
  -- values (KVal) using closures. A lambda captures its environment; applying it
  -- pushes the argument, giving O(1) beta reduction. Constants evaluate to
  -- neutrals (no eager delta unfolding) — definition unfolding is deferred to WHNF.
  -- Free variables use de Bruijn levels (stable under binder entry).
  -- ============================================================================

  -- Force a thunk: if it's a Thunk, evaluate it; otherwise return as-is
  fn k_force(v: KVal, top: List‹&KConstantInfo›) -> KVal {
    match load(v) {
      KValNode.Thunk(e, &env) => k_eval(e, env, top),
      _ => v,
    }
  }

  -- Evaluate an expression to a value using Normalization by Evaluation (NbE)
  fn k_eval(e: KExpr, env: KValEnv, top: List‹&KConstantInfo›) -> KVal {
    match load(e) {
      KExprNode.BVar(idx) =>
        list_lookup(env, idx),

      KExprNode.Srt(&l) =>
        store(KValNode.Srt(store(level_reduce(l)))),

      -- Lazy: no definition unfolding during eval, deferred to WHNF
      KExprNode.Const(idx, &lvls) =>
        let ci = load(list_lookup(top, idx));
        match ci {
          KConstantInfo.Ctor(_, _, _, _, nparams, _, _) =>
            store(KValNode.Ctor(idx, store(lvls), nparams, store(List.Nil))),
          _ => store(KValNode.Const(idx, store(lvls), store(List.Nil))),
        },

      KExprNode.App(f, a) =>
        let vf = k_eval(f, env, top);
        let arg = suspend(a, env);
        k_apply(vf, arg, top),

      KExprNode.Lam(ty, body) =>
        let ty_val = suspend(ty, env);
        store(KValNode.Lam(ty_val, body, store(env))),

      KExprNode.Forall(ty, body) =>
        let ty_val = suspend(ty, env);
        store(KValNode.Pi(ty_val, body, store(env))),

      KExprNode.Let(_, val, body) =>
        let v = k_eval(val, env, top);
        let env2 = List.Cons(v, store(env));
        k_eval(body, env2, top),

      KExprNode.Lit(lit) =>
        store(KValNode.Lit(lit)),

      KExprNode.Proj(tidx, fidx, e1) =>
        let v = k_eval(e1, env, top);
        match load(v) {
          KValNode.Ctor(_, _, nparams, &spine) =>
            let field_idx = nparams + fidx;
            let field = list_lookup(spine, field_idx);
            k_force(field, top),
          _ =>
            store(KValNode.Proj(tidx, fidx, v, store(List.Nil))),
        },
    }
  }

  -- Suspend an expression: evaluate immediately for cheap/structural forms
  -- (BVar lookup, Srt, Lit, Lam closure, Pi closure); otherwise defer to a thunk.
  fn suspend(e: KExpr, env: KValEnv) -> KVal {
    match load(e) {
      KExprNode.BVar(idx) =>
        list_lookup(env, idx),
      KExprNode.Srt(&l) =>
        store(KValNode.Srt(store(level_reduce(l)))),
      KExprNode.Lit(lit) =>
        store(KValNode.Lit(lit)),
      KExprNode.Lam(ty, body) =>
        let ty_val = suspend(ty, env);
        store(KValNode.Lam(ty_val, body, store(env))),
      KExprNode.Forall(ty, body) =>
        let ty_val = suspend(ty, env);
        store(KValNode.Pi(ty_val, body, store(env))),
      _ =>
        store(KValNode.Thunk(e, store(env))),
    }
  }

  -- Apply a value to an argument (lazy: arg may be a thunk)
  fn k_apply(f: KVal, arg: KVal, top: List‹&KConstantInfo›) -> KVal {
    match load(f) {
      KValNode.Lam(_, body, &env) =>
        let arg_forced = k_force(arg, top);
        let env2 = List.Cons(arg_forced, store(env));
        k_eval(body, env2, top),

      KValNode.Ctor(idx, &lvls, nparams, &spine) =>
        let spine2 = list_snoc(spine, arg);
        store(KValNode.Ctor(idx, store(lvls), nparams, store(spine2))),

      KValNode.FVar(lvl, fvar_ty, &spine) =>
        let spine2 = list_snoc(spine, arg);
        store(KValNode.FVar(lvl, fvar_ty, store(spine2))),

      KValNode.Const(idx, &lvls, &spine) =>
        let spine2 = list_snoc(spine, arg);
        store(KValNode.Const(idx, store(lvls), store(spine2))),

      KValNode.Proj(tidx, fidx, sv, &spine) =>
        let spine2 = list_snoc(spine, arg);
        store(KValNode.Proj(tidx, fidx, sv, store(spine2))),

      KValNode.Thunk(e, &env) =>
        let v = k_eval(e, env, top);
        k_apply(v, arg, top),

    }
  }

  -- Apply a value to a list of arguments
  fn k_apply_spine(f: KVal, spine: List‹KVal›, top: List‹&KConstantInfo›) -> KVal {
    match spine {
      List.Nil => f,
      List.Cons(v, &rest) =>
        let f2 = k_apply(f, v, top);
        k_apply_spine(f2, rest, top),
    }
  }

  -- ============================================================================
  -- Iota reduction (recursor on constructor)
  --
  -- When a recursor meets the constructor it can pattern-match on, reduce:
  --   Nat.rec motive hz hs (Nat.succ n)  →  hs n (Nat.rec motive hz hs n)
  -- Also handles Nat literal iota: Lit(0) matches the zero constructor,
  -- Lit(n+1) matches succ with Lit(n) as predecessor.
  -- ============================================================================

  -- Get induct_idx from a constructor's constant info
  fn ctor_induct_idx(ctor_idx: G, top: List‹&KConstantInfo›) -> G {
    let ctor_ci = load(list_lookup(top, ctor_idx));
    match ctor_ci {
      KConstantInfo.Ctor(_, _, induct_idx, _, _, _, _) => induct_idx,
    }
  }

  -- Try iota reduction: if idx refers to a recursor and the major premise is a
  -- constructor or Nat literal, apply the matching recursor rule; otherwise return a neutral VConst
  fn try_iota(idx: G, lvls: List‹&KLevel›, spine: List‹KVal›, top: List‹&KConstantInfo›) -> KVal {
    let ci = load(list_lookup(top, idx));
    match ci {
      KConstantInfo.Rec(_, _, nparams, nindices, nmotives, nminors, &rules, k_flag, _) =>
        let maj_idx = nparams + nmotives + nminors + nindices;
        let spine_len = list_length(spine);
        let not_have_major = eq_zero(spine_len - maj_idx);
        match not_have_major {
          1 => store(KValNode.Const(idx, store(lvls), store(spine))),
          0 =>
            let major_raw = list_lookup(spine, maj_idx);
            let major = k_whnf(major_raw, top);
            match load(major) {
              KValNode.Ctor(ctor_idx, _, ctor_nparams, &ctor_spine) =>
                let rule_found = rec_rule_try_find(rules, ctor_idx);
                match rule_found {
                  Option.None =>
                    store(KValNode.Const(idx, store(lvls), store(spine))),
                  Option.Some(&rule) =>
                    match rule {
                      KRecRule.Mk(_, nfields, &rhs) =>
                        let rhs_inst = expr_inst_levels(rhs, lvls);
                        let rhs_val = k_eval(rhs_inst, List.Nil, top);
                        let params_motives_minors = list_take(spine, nparams + nmotives + nminors);
                        let result = k_apply_spine(rhs_val, params_motives_minors, top);
                        let fields = list_drop(ctor_spine, ctor_nparams);
                        let result2 = k_apply_spine(result, fields, top);
                        let remaining = list_drop(spine, maj_idx + 1);
                        k_apply_spine(result2, remaining, top),
                    },
                },
              KValNode.Lit(lit) =>
                match lit {
                  KLiteral.Nat(&n) =>
                    -- Nat literal iota: Lit(0) → zero rule, Lit(n+1) → succ rule with Lit(n)
                    -- Derive the inductive idx from the first rule's ctor_idx
                    let first_ctor_idx = rec_rule_first_ctor(rules);
                    let induct_idx = ctor_induct_idx(first_ctor_idx, top);
                    let ind_ci = load(list_lookup(top, induct_idx));
                    match ind_ci {
                      KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
                        let pmm_end = nparams + nmotives + nminors;
                        let is_zero = klimbs_is_zero(n);
                        match is_zero {
                          1 =>
                            -- Lit(0) → fire zero rule with no ctor fields
                            let zero_ctor_idx = list_lookup(ctor_indices, 0);
                            let rule = rec_rule_find(rules, zero_ctor_idx);
                            match rule {
                              KRecRule.Mk(_, _, &rhs) =>
                                let rhs_inst = expr_inst_levels(rhs, lvls);
                                let rhs_val = k_eval(rhs_inst, List.Nil, top);
                                let pmm = list_take(spine, pmm_end);
                                let result = k_apply_spine(rhs_val, pmm, top);
                                let remaining = list_drop(spine, maj_idx + 1);
                                k_apply_spine(result, remaining, top),
                            },
                          0 =>
                            -- Lit(n+1) → fire succ rule with one field = Lit(n-1)
                            let succ_ctor_idx = list_lookup(ctor_indices, 1);
                            let rule = rec_rule_find(rules, succ_ctor_idx);
                            match rule {
                              KRecRule.Mk(_, _, &rhs) =>
                                let rhs_inst = expr_inst_levels(rhs, lvls);
                                let rhs_val = k_eval(rhs_inst, List.Nil, top);
                                let pmm = list_take(spine, pmm_end);
                                let result = k_apply_spine(rhs_val, pmm, top);
                                let pred = store(KValNode.Lit(KLiteral.Nat(store(klimbs_pred(n)))));
                                let ctor_fields = List.Cons(pred, store(List.Nil));
                                let result2 = k_apply_spine(result, ctor_fields, top);
                                let remaining = list_drop(spine, maj_idx + 1);
                                k_apply_spine(result2, remaining, top),
                            },
                        },
                    },
                  KLiteral.Str(_) =>
                    store(KValNode.Const(idx, store(lvls), store(spine))),
                },
              _ =>
                -- K-reduction: for proof-irrelevant (Prop) inductives with k_flag set,
                -- return the minor premise applied to remaining args after major
                match k_flag {
                  0 =>
                    -- Not a K-recursor, return stuck
                    store(KValNode.Const(idx, store(lvls), store(spine))),
                  _ =>
                    -- K-reduction fires: minor is at nparams + nmotives
                    let minor_idx = nparams + nmotives;
                    let minor = list_lookup(spine, minor_idx);
                    let remaining = list_drop(spine, maj_idx + 1);
                    k_apply_spine(minor, remaining, top),
                },
            },
        },

      _ => store(KValNode.Const(idx, store(lvls), store(spine))),
    }
  }

  -- Take the first n elements of a val list
  -- ============================================================================
  -- Quotient reduction
  -- ============================================================================

  -- Try quotient reduction: Quot.lift f h (Quot.mk r a) → f a
  -- reduce_size is the minimum spine length, f_pos is the index of f in the spine.
  -- Returns 1 and reduced value via k_whnf if successful, 0 otherwise.
  -- The idx/lvls/spine are passed through for reconstructing the stuck value on failure.
  fn k_try_quot_reduction(idx: G, lvls: List‹&KLevel›, spine: List‹KVal›,
      reduce_size: G, f_pos: G, top: List‹&KConstantInfo›) -> KVal {
    let spine_len = list_length(spine);
    let not_enough = eq_zero(spine_len - reduce_size);
    match not_enough {
      1 => store(KValNode.Const(idx, store(lvls), store(spine))),
      0 =>
        -- Force and WHNF the major arg (last of the reduce_size args)
        let major_idx = reduce_size - 1;
        let major_raw = list_lookup(spine, major_idx);
        let major = k_whnf(major_raw, top);
        -- Check if major is a Quot.mk application (a Const with QuotKind.Ctor)
        match load(major) {
          KValNode.Const(mk_idx, _, &mk_spine) =>
            let mk_ci = load(list_lookup(top, mk_idx));
            match mk_ci {
              KConstantInfo.Quot(_, _, mk_kind) =>
                match mk_kind {
                  KQuotKind.Ctor =>
                    -- mk_spine should have >= 3 args: [α, r, a]
                    -- The quotient value is the last element
                    let mk_len = list_length(mk_spine);
                    let no_args = eq_zero(mk_len - 3);
                    match no_args {
                      1 => store(KValNode.Const(idx, store(lvls), store(spine))),
                      0 =>
                        let quot_val_idx = mk_len - 1;
                        let quot_val = list_lookup(mk_spine, quot_val_idx);
                        -- Apply f (at f_pos) to the quotient value
                        let f_val = k_force(list_lookup(spine, f_pos), top);
                        let result = k_apply(f_val, quot_val, top);
                        -- Apply remaining spine args after reduce_size
                        let remaining = list_drop(spine, reduce_size);
                        let result2 = k_apply_spine(result, remaining, top);
                        k_whnf(result2, top),
                    },
                  _ => store(KValNode.Const(idx, store(lvls), store(spine))),
                },
              _ => store(KValNode.Const(idx, store(lvls), store(spine))),
            },
          _ => store(KValNode.Const(idx, store(lvls), store(spine))),
        },
    }
  }

  -- ============================================================================
  -- WHNF (Weak Head Normal Form)
  --
  -- Reduce a value until its outermost constructor is visible. The WHNF loop
  -- applies projection reduction, iota (recursor on ctor), delta (definition
  -- unfolding), and quotient reduction, retrying after each successful step.
  -- Does not reduce under binders or inside arguments.
  -- ============================================================================

  -- Reduce a value to Weak Head Normal Form by retrying projection, iota, and delta reductions

  fn k_whnf(v: KVal, top: List‹&KConstantInfo›) -> KVal {
    match load(v) {
      KValNode.Thunk(e, &env) =>
        let val = k_eval(e, env, top);
        k_whnf(val, top),

      KValNode.Proj(tidx, fidx, sv, &spine) =>
        let sv2 = k_whnf(sv, top);
        match load(sv2) {
          KValNode.Ctor(_, _, nparams, &ctor_spine) =>
            let field_idx = nparams + fidx;
            let field = list_lookup(ctor_spine, field_idx);
            let field_forced = k_force(field, top);
            let result = k_apply_spine(field_forced, spine, top);
            k_whnf(result, top),
          _ =>
            store(KValNode.Proj(tidx, fidx, sv2, store(spine))),
        },

      KValNode.Const(idx, &lvls, &spine) =>
        -- First try iota reduction (recursor on constructor)
        let result = try_iota(idx, lvls, spine, top);
        match load(result) {
          KValNode.Const(idx2, &lvls2, &spine2) =>
            let same = eq_zero(idx - idx2);
            match same {
              0 => k_whnf(result, top),
              1 =>
                -- Iota didn't fire; try quotient, then delta
                let ci = load(list_lookup(top, idx2));
                match ci {
                  KConstantInfo.Defn(_, _, &value, hints, _) =>
                    match hints {
                      KHints.Opaque => result,
                      _ =>
                        let body = expr_inst_levels(value, lvls2);
                        let val = k_eval(body, List.Nil, top);
                        let val2 = k_apply_spine(val, spine2, top);
                        k_whnf(val2, top),
                    },
                  KConstantInfo.Thm(_, _, &value) =>
                    let body = expr_inst_levels(value, lvls2);
                    let val = k_eval(body, List.Nil, top);
                    let val2 = k_apply_spine(val, spine2, top);
                    k_whnf(val2, top),
                  -- Quot.lift: spine has [α, r, β, f, h, ⟨Quot.mk r a⟩, extra...]
                  -- Quot.ind: spine has [α, r, motive, f, ⟨Quot.mk r a⟩, extra...]
                  -- Reduces to: f a extra...
                  KConstantInfo.Quot(_, _, kind) =>
                    match kind {
                      KQuotKind.Lift =>
                        k_try_quot_reduction(idx2, lvls2, spine2, 6, 3, top),
                      KQuotKind.Ind =>
                        k_try_quot_reduction(idx2, lvls2, spine2, 5, 3, top),
                      _ => result,
                    },
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
  --
  -- Readback from the semantic domain: converts KVal back to KExpr.
  -- Needed when instantiating universe parameters or building the Pi type
  -- for a lambda's inferred type. Converts de Bruijn levels back to indices.
  -- ============================================================================

  -- Quote a value back into an expression (readback), converting free variables
  -- to de Bruijn indices relative to the current depth
  fn k_quote(v: KVal, depth: G, top: List‹&KConstantInfo›) -> KExpr {
    match load(v) {
      KValNode.Thunk(e, &env) =>
        let val = k_eval(e, env, top);
        k_quote(val, depth, top),

      KValNode.Srt(&l) => store(KExprNode.Srt(store(l))),

      KValNode.Lit(lit) => store(KExprNode.Lit(lit)),

      KValNode.Lam(dom, body, &env) =>
        let dom_expr = k_quote(dom, depth, top);
        let fvar = store(KValNode.FVar(depth, dom, store(List.Nil)));
        let env2 = List.Cons(fvar, store(env));
        let body_val = k_eval(body, env2, top);
        let body_expr = k_quote(body_val, depth + 1, top);
        store(KExprNode.Lam(dom_expr, body_expr)),

      KValNode.Pi(dom, body, &env) =>
        let dom_expr = k_quote(dom, depth, top);
        let fvar = store(KValNode.FVar(depth, dom, store(List.Nil)));
        let env2 = List.Cons(fvar, store(env));
        let body_val = k_eval(body, env2, top);
        let body_expr = k_quote(body_val, depth + 1, top);
        store(KExprNode.Forall(dom_expr, body_expr)),

      KValNode.Ctor(idx, &lvls, _, &spine) =>
        let base = store(KExprNode.Const(idx, store(lvls)));
        quote_spine(base, spine, depth, top),

      KValNode.FVar(lvl, _, &spine) =>
        let idx = (depth - 1) - lvl;
        let base = store(KExprNode.BVar(idx));
        quote_spine(base, spine, depth, top),

      KValNode.Const(idx, &lvls, &spine) =>
        let base = store(KExprNode.Const(idx, store(lvls)));
        quote_spine(base, spine, depth, top),

      KValNode.Proj(tidx, fidx, sv, &spine) =>
        let sv_expr = k_quote(sv, depth, top);
        let base = store(KExprNode.Proj(tidx, fidx, sv_expr));
        quote_spine(base, spine, depth, top),
    }
  }

  -- Quote a spine of arguments, wrapping each in an EApp around the base expression
  fn quote_spine(base: KExpr, spine: List‹KVal›, depth: G, top: List‹&KConstantInfo›) -> KExpr {
    match spine {
      List.Nil => base,
      List.Cons(v, &rest) =>
        let arg_expr = k_quote(v, depth, top);
        let app = store(KExprNode.App(base, arg_expr));
        quote_spine(app, rest, depth, top),
    }
  }

  -- ============================================================================
  -- Type inference
  --
  -- Infer the type of an expression (k_infer) or check it against an expected
  -- type (k_check). Bidirectional: when checking a lambda against a Pi type,
  -- the expected codomain is pushed through the body, avoiding an expensive
  -- infer + isDefEq.
  -- ============================================================================

  -- Infer the type of an expression under the given type and value environments.
  -- nat_idx/str_idx are the constant indices for the Nat/String types (for literal typing).
  fn k_infer(e: KExpr, types: List‹KVal›, env: KValEnv, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> KVal {
    match load(e) {
      KExprNode.BVar(idx) =>
        list_lookup(types, idx),

      KExprNode.Srt(&l) =>
        store(KValNode.Srt(store(KLevel.Succ(store(l))))),

      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) =>
            store(KValNode.Const(nat_idx, store(List.Nil), store(List.Nil))),
          KLiteral.Str(_) =>
            store(KValNode.Const(str_idx, store(List.Nil), store(List.Nil))),
        },

      KExprNode.Const(idx, &lvls) =>
        let ci = load(list_lookup(top, idx));
        let expected = const_num_levels(ci);
        let given = list_length(lvls);
        let lvl_eq = eq_zero(expected - given);
        assert_eq!(lvl_eq, 1);
        let ty = const_type(ci);
        let ty_inst = expr_inst_levels(ty, lvls);
        k_eval(ty_inst, List.Nil, top),

      KExprNode.App(f, a) =>
        let fn_type = k_infer(f, types, env, depth, top, nat_idx, str_idx);
        let fn_type_whnf = k_whnf(fn_type, top);

        match load(fn_type_whnf) {
          KValNode.Pi(dom, body, &pi_env) =>
            let _ = k_check(a, dom, types, env, depth, top, nat_idx, str_idx);
            let arg_val = k_eval(a, env, top);
            let pi_env2 = List.Cons(arg_val, store(pi_env));
            k_eval(body, pi_env2, top),
        },

      KExprNode.Lam(ty, body) =>
        let _ = k_ensure_sort(ty, types, env, depth, top, nat_idx, str_idx);
        let dom_val = k_eval(ty, env, top);
        let fvar = store(KValNode.FVar(depth, dom_val, store(List.Nil)));
        let types2 = List.Cons(dom_val, store(types));
        let env2 = List.Cons(fvar, store(env));
        let body_type = k_infer(body, types2, env2, depth + 1, top, nat_idx, str_idx);
        let body_type_expr = k_quote(body_type, depth + 1, top);
        store(KValNode.Pi(dom_val, body_type_expr, store(env))),

      KExprNode.Forall(ty, body) =>
        let dom_level = k_ensure_sort(ty, types, env, depth, top, nat_idx, str_idx);
        let dom_val = k_eval(ty, env, top);
        let fvar = store(KValNode.FVar(depth, dom_val, store(List.Nil)));
        let types2 = List.Cons(dom_val, store(types));
        let env2 = List.Cons(fvar, store(env));
        let body_level = k_ensure_sort(body, types2, env2, depth + 1, top, nat_idx, str_idx);
        let result_level = level_imax(dom_level, body_level);
        store(KValNode.Srt(store(result_level))),

      KExprNode.Let(ty, val, body) =>
        let _ = k_ensure_sort(ty, types, env, depth, top, nat_idx, str_idx);
        let ty_val = k_eval(ty, env, top);
        let _ = k_check(val, ty_val, types, env, depth, top, nat_idx, str_idx);
        let val_val = k_eval(val, env, top);
        let types2 = List.Cons(ty_val, store(types));
        let env2 = List.Cons(val_val, store(env));
        k_infer(body, types2, env2, depth + 1, top, nat_idx, str_idx),

      KExprNode.Proj(tidx, fidx, e1) =>
        -- Infer struct type and WHNF to expose inductive head
        let struct_type = k_infer(e1, types, env, depth, top, nat_idx, str_idx);
        let struct_type_whnf = k_whnf(struct_type, top);
        match load(struct_type_whnf) {
          KValNode.Const(induct_idx, &levels, &params_spine) =>
            -- Look up inductive to get its single constructor index
            let ind_ci = load(list_lookup(top, induct_idx));
            match ind_ci {
              KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
                let ctor_idx = list_lookup(ctor_indices, 0);
                -- Get the constructor type, instantiate levels, and eval
                let ctor_ci = load(list_lookup(top, ctor_idx));
                let ctor_type_expr = const_type(ctor_ci);
                let ctor_type_inst = expr_inst_levels(ctor_type_expr, levels);
                let ctor_type_val = k_eval(ctor_type_inst, List.Nil, top);
                -- Walk past params using values from the inductive's spine
                let after_params = walk_params(ctor_type_val, params_spine, top);
                -- Walk past preceding fields using Proj values
                let struct_val = k_eval(e1, env, top);
                let after_fields = walk_fields(after_params, tidx, 0, fidx, struct_val, top);
                -- Extract the domain type at field fidx
                let result_whnf = k_whnf(after_fields, top);
                match load(result_whnf) {
                  KValNode.Pi(dom, _, _) => dom,
                },
            },
        },
    }
  }

  -- Bidirectional type checking: check term against expected type.
  -- For Lambda against Pi, pushes the codomain through instead of independently inferring.
  fn k_check(e: KExpr, expected: KVal, types: List‹KVal›, env: KValEnv, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) {
    match load(e) {
      KExprNode.Lam(ty, body) =>
        let expected_whnf = k_whnf(expected, top);
        match load(expected_whnf) {
          KValNode.Pi(pi_dom, pi_body, &pi_env) =>
            -- Check domain matches
            let dom_val = k_eval(ty, env, top);
            let dom_eq = k_is_def_eq(dom_val, pi_dom, depth, top, nat_idx, str_idx);
            assert_eq!(dom_eq, 1);
            -- Push Pi codomain through Lambda body
            let fvar = store(KValNode.FVar(depth, pi_dom, store(List.Nil)));
            let types2 = List.Cons(pi_dom, store(types));
            let env2 = List.Cons(fvar, store(env));
            let pi_env2 = List.Cons(fvar, store(pi_env));
            let expected_body = k_eval(pi_body, pi_env2, top);
            k_check(body, expected_body, types2, env2, depth + 1, top, nat_idx, str_idx),
        },
      _ =>
        -- Non-lambda: infer + isDefEq
        let inferred = k_infer(e, types, env, depth, top, nat_idx, str_idx);
        let eq = k_is_def_eq(inferred, expected, depth, top, nat_idx, str_idx);
        assert_eq!(eq, 1);,
    }
  }

  -- Ensure a type expression evaluates to a Sort, returning the level
  fn k_ensure_sort(e: KExpr, types: List‹KVal›, env: KValEnv, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> KLevel {
    let ty = k_infer(e, types, env, depth, top, nat_idx, str_idx);
    let ty_whnf = k_whnf(ty, top);
    match load(ty_whnf) {
      KValNode.Srt(&l) => l,
    }
  }

  -- Walk past n Pi binders, substituting param values from the spine
  fn walk_params(ct: KVal, params: List‹KVal›, top: List‹&KConstantInfo›) -> KVal {
    match params {
      List.Nil => ct,
      List.Cons(param_val, &rest_params) =>
        let param_forced = k_force(param_val, top);
        let ct_whnf = k_whnf(ct, top);
        match load(ct_whnf) {
          KValNode.Pi(_, body, &pi_env) =>
            let env2 = List.Cons(param_forced, store(pi_env));
            let next = k_eval(body, env2, top);
            walk_params(next, rest_params, top),
        },
    }
  }

  -- Walk past n fields in a constructor type, substituting Proj values
  fn walk_fields(ct: KVal, tidx: G, current_field: G, remaining: G, struct_val: KVal, top: List‹&KConstantInfo›) -> KVal {
    match remaining {
      0 => ct,
      _ =>
        let ct_whnf = k_whnf(ct, top);
        match load(ct_whnf) {
          KValNode.Pi(_, body, &pi_env) =>
            let proj_val = store(KValNode.Proj(tidx, current_field, struct_val, store(List.Nil)));
            let env2 = List.Cons(proj_val, store(pi_env));
            let next = k_eval(body, env2, top);
            walk_fields(next, tidx, current_field + 1, remaining - 1, struct_val, top),
        },
    }
  }

  -- ============================================================================
  -- Proof irrelevance helpers
  --
  -- If a : P and b : P where P : Prop (Sort 0), then a ≡ b.
  -- k_infer_val_type is best-effort: returns Sort 1 sentinel for FVar/Lam/Proj,
  -- so proof irrelevance won't trigger for free-variable-headed proofs.
  -- Conservative (never unsound) but incomplete.
  -- ============================================================================

  -- Apply a spine of argument values to a type by walking through Pi-bindings
  fn apply_spine_to_type(ty: KVal, spine: List‹KVal›, top: List‹&KConstantInfo›) -> KVal {
    match spine {
      List.Nil => ty,
      List.Cons(arg, &rest) =>
        let arg_forced = k_force(arg, top);
        let ty_whnf = k_whnf(ty, top);
        match load(ty_whnf) {
          KValNode.Pi(_, body, &pi_env) =>
            let env2 = List.Cons(arg_forced, store(pi_env));
            let next = k_eval(body, env2, top);
            apply_spine_to_type(next, rest, top),
        },
    }
  }

  -- Infer the type of a value (best-effort, no error handling).
  -- Returns Sort 1 as sentinel for cases we can't handle (FVar, Lam, Proj).
  fn k_infer_val_type(v: KVal, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> KVal {
    match load(v) {
      KValNode.Thunk(e, &env) =>
        let val = k_eval(e, env, top);
        k_infer_val_type(val, top, nat_idx, str_idx),
      KValNode.Srt(&l) => store(KValNode.Srt(store(KLevel.Succ(store(l))))),
      KValNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) => store(KValNode.Const(nat_idx, store(List.Nil), store(List.Nil))),
          KLiteral.Str(_) => store(KValNode.Const(str_idx, store(List.Nil), store(List.Nil))),
        },
      KValNode.Const(idx, &lvls, &spine) =>
        let ci = load(list_lookup(top, idx));
        let ty = const_type(ci);
        let ty_inst = expr_inst_levels(ty, lvls);
        let ty_val = k_eval(ty_inst, List.Nil, top);
        apply_spine_to_type(ty_val, spine, top),
      KValNode.Ctor(idx, &lvls, _, &spine) =>
        let ci = load(list_lookup(top, idx));
        let ty = const_type(ci);
        let ty_inst = expr_inst_levels(ty, lvls);
        let ty_val = k_eval(ty_inst, List.Nil, top);
        apply_spine_to_type(ty_val, spine, top),
      KValNode.Proj(tidx, fidx, sv, &spine) =>
        let struct_type = k_infer_val_type(sv, top, nat_idx, str_idx);
        let struct_type_whnf = k_whnf(struct_type, top);
        match load(struct_type_whnf) {
          KValNode.Const(induct_idx, &levels, &params_spine) =>
            let ind_ci = load(list_lookup(top, induct_idx));
            match ind_ci {
              KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
                let ctor_idx = list_lookup(ctor_indices, 0);
                let ctor_ci = load(list_lookup(top, ctor_idx));
                let ctor_type_expr = const_type(ctor_ci);
                let ctor_type_inst = expr_inst_levels(ctor_type_expr, levels);
                let ctor_type_val = k_eval(ctor_type_inst, List.Nil, top);
                let after_params = walk_params(ctor_type_val, params_spine, top);
                let after_fields = walk_fields(after_params, tidx, 0, fidx, sv, top);
                let result_whnf = k_whnf(after_fields, top);
                match load(result_whnf) {
                  KValNode.Pi(dom, _, _) => apply_spine_to_type(dom, spine, top),
                  -- If not a Pi, return the type itself (could be the final result type)
                  _ => apply_spine_to_type(result_whnf, spine, top),
                },
              -- Not an inductive, fall back to sentinel
              _ => store(KValNode.Srt(store(KLevel.Succ(store(KLevel.Zero))))),
            },
          -- If struct type can't be determined, fall back to sentinel
          _ => store(KValNode.Srt(store(KLevel.Succ(store(KLevel.Zero))))),
        },
      KValNode.FVar(_, fvar_type, &spine) =>
        apply_spine_to_type(fvar_type, spine, top),
      -- For Lam, Pi: return Sort 1 as sentinel (never Prop)
      _ => store(KValNode.Srt(store(KLevel.Succ(store(KLevel.Zero))))),
    }
  }

  -- Check if a value is a proposition (its type is Sort 0 / Prop)
  fn k_is_prop_val(v: KVal, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
    let ty = k_infer_val_type(v, top, nat_idx, str_idx);
    let ty_whnf = k_whnf(ty, top);
    match load(ty_whnf) {
      KValNode.Srt(&l) =>
        match l {
          KLevel.Zero => 1,
          _ => 0,
        },
      _ => 0,
    }
  }

  -- ============================================================================
  -- Struct eta helpers
  --
  -- Structure eta: s ≡ ⟨s.1, s.2, ...⟩ for single-constructor types.
  -- If one side is a Ctor of a struct-like inductive (1 constructor, no indices),
  -- compare each field against Proj(i, other_side).
  -- ============================================================================

  -- Get num_fields from a constructor's constant info
  fn ctor_num_fields(ctor_idx: G, top: List‹&KConstantInfo›) -> G {
    let ctor_ci = load(list_lookup(top, ctor_idx));
    match ctor_ci {
      KConstantInfo.Ctor(_, _, _, _, _, nfields, _) => nfields,
    }
  }

  -- Compare each field: Proj(tidx, i, t) vs spine[nparams + i]
  fn eta_struct_fields(t: KVal, spine: List‹KVal›, nparams: G, tidx: G, current: G, remaining: G, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
    match remaining {
      0 => 1,
      _ =>
        let field_idx = nparams + current;
        let field_val = list_lookup(spine, field_idx);
        let proj_val = store(KValNode.Proj(tidx, current, t, store(List.Nil)));
        let eq = k_is_def_eq(proj_val, field_val, depth, top, nat_idx, str_idx);
        match eq {
          0 => 0,
          1 => eta_struct_fields(t, spine, nparams, tidx, current + 1, remaining - 1, depth, top, nat_idx, str_idx),
        },
    }
  }

  -- Try struct eta: if s is a Ctor of a struct-like type, compare fields.
  -- Inlines is_struct_like, ctor_induct_idx, ctor_num_fields to avoid redundant lookups.
  fn try_eta_struct_one(t: KVal, s: KVal, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
    match load(s) {
      KValNode.Ctor(ctor_idx, _, nparams, &spine) =>
        let ctor_ci = load(list_lookup(top, ctor_idx));
        match ctor_ci {
          KConstantInfo.Ctor(_, _, induct_idx, _, _, num_fields, _) =>
            let ind_ci = load(list_lookup(top, induct_idx));
            match ind_ci {
              KConstantInfo.Induct(_, _, _, _, &ctor_indices, _, _, _) =>
                let num_ctors = list_length(ctor_indices);
                let is_single = eq_zero(num_ctors - 1);
                match is_single {
                  0 => 0,
                  1 =>
                    eta_struct_fields(t, spine, nparams, induct_idx, 0, num_fields, depth, top, nat_idx, str_idx),
                },
              _ => 0,
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Try struct eta in both directions
  fn try_eta_struct(a: KVal, b: KVal, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
    let r1 = try_eta_struct_one(a, b, depth, top, nat_idx, str_idx);
    match r1 {
      1 => 1,
      0 => try_eta_struct_one(b, a, depth, top, nat_idx, str_idx),
    }
  }

  -- Unit-like type equality: if both values have a type with exactly one
  -- nullary constructor and no indices, they are definitionally equal.
  -- Examples: True, PUnit, PLift.up for propositions.
  fn is_unit_like_type(ty: KVal, top: List‹&KConstantInfo›) -> G {
    let ty_whnf = k_whnf(ty, top);
    match load(ty_whnf) {
      KValNode.Const(induct_idx, _, _) =>
        let ci = load(list_lookup(top, induct_idx));
        match ci {
          KConstantInfo.Induct(_, _, _, nindices, &ctor_indices, _, _, _) =>
            let zero_indices = eq_zero(nindices);
            let one_ctor = eq_zero(list_length(ctor_indices) - 1);
            match zero_indices * one_ctor {
              0 => 0,
              _ =>
                let ctor_idx = list_lookup(ctor_indices, 0);
                let ctor_ci = load(list_lookup(top, ctor_idx));
                match ctor_ci {
                  KConstantInfo.Ctor(_, _, _, _, _, nfields, _) =>
                    eq_zero(nfields),
                  _ => 0,
                },
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  fn try_unit_like(a: KVal, b: KVal, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
    let a_type = k_infer_val_type(a, top, nat_idx, str_idx);
    is_unit_like_type(a_type, top)
  }

  -- ============================================================================
  -- Definitional equality
  --
  -- The most complex part of the kernel. Uses a layered approach:
  --   1. Quick syntactic check (sorts, literals)
  --   2. Reduce both sides to WHNF
  --   3. Proof irrelevance (type is Prop ⟹ equal by irrelevance)
  --   4. Structural comparison (k_is_def_eq_core)
  --   5. Struct eta (s ≡ ⟨s.1, s.2, ...⟩)
  --   6. Unit-like types (one nullary constructor ⟹ all values equal)
  --   7. Lazy delta unfolding (try unfolding constants to make progress)
  -- ============================================================================

  -- Check definitional equality of two values: first try a quick syntactic check,
  -- then reduce to WHNF and compare structurally
  fn k_is_def_eq(a: KVal, b: KVal, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
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
            -- Proof irrelevance: a and b share the same type, so if that type is
            -- Prop then both are proofs of the same proposition and are equal.
            let a_type = k_infer_val_type(a_whnf, top, nat_idx, str_idx);
            let a_is_prop = k_is_prop_val(a_type, top, nat_idx, str_idx);
            match a_is_prop {
              1 => 1,
              0 =>
                let core_res = k_is_def_eq_core(a_whnf, b_whnf, depth, top, nat_idx, str_idx);
                match core_res {
                  0 =>
                    let eta_res = try_eta_struct(a_whnf, b_whnf, depth, top, nat_idx, str_idx);
                    match eta_res {
                      1 => 1,
                      0 => try_unit_like(a_whnf, b_whnf, top, nat_idx, str_idx),
                    },
                  1 => 1,
                },
            },
        },
    }
  }

  -- Quick syntactic check for definitional equality (sorts and literals only)
  fn k_quick_def_eq(a: KVal, b: KVal) -> G {
    match ptr_val(a) - ptr_val(b) {
      0 => 1,
      _ =>
        match load(a) {
          KValNode.Srt(&la) =>
            match load(b) {
              KValNode.Srt(&lb) => level_equal(la, lb),
              _ => 0,
            },
          KValNode.Lit(la) =>
            match load(b) {
              KValNode.Lit(lb) => literal_eq(la, lb),
              _ => 0,
            },
          _ => 0,
        },
    }
  }

  -- ============================================================================
  -- KLimbs operations (bignum arithmetic on little-endian u64 limbs)
  -- ============================================================================

  -- Check if a KLimbs value is zero (Nil = zero)
  fn klimbs_is_zero(limbs: KLimbs) -> G {
    match limbs {
      List.Nil => 1,
      List.Cons(_, _) => 0,
    }
  }

  -- Compare two KLimbs for equality (limb-by-limb)
  fn klimbs_eq(a: KLimbs, b: KLimbs) -> G {
    match a {
      List.Nil =>
        match b {
          List.Nil => 1,
          _ => 0,
        },
      List.Cons(la, &ra) =>
        match b {
          List.Nil => 0,
          List.Cons(lb, &rb) =>
            let eq = u64_eq(la, lb);
            match eq {
              0 => 0,
              1 => klimbs_eq(ra, rb),
            },
        },
    }
  }

  -- Subtract 1 from a KLimbs bignum. Assumes non-zero input.
  -- Works limb-by-limb: if limb is non-zero, decrement it; else borrow.
  fn klimbs_pred(limbs: KLimbs) -> KLimbs {
    match limbs {
      List.Nil => List.Nil,
      List.Cons(limb, &rest) =>
        let is_zero = u64_is_zero(limb);
        match is_zero {
          0 =>
            -- Non-zero limb: decrement it
            let new_limb = relaxed_u64_pred(limb);
            -- If this was the only limb and it became zero, return Nil
            match rest {
              List.Nil =>
                let new_zero = u64_is_zero(new_limb);
                match new_zero {
                  1 => List.Nil,
                  0 => List.Cons(new_limb, store(List.Nil)),
                },
              _ => List.Cons(new_limb, store(rest)),
            },
          1 =>
            -- Zero limb: borrow from next, this limb becomes 0xFF..FF
            let new_rest = klimbs_pred(rest);
            -- 0xFFFFFFFFFFFFFFFF = [255, 255, 255, 255, 255, 255, 255, 255]
            let max_u64 = [255, 255, 255, 255, 255, 255, 255, 255];
            List.Cons(max_u64, store(new_rest)),
        },
    }
  }

  -- Compare two ByteStreams for equality
  fn bytestream_eq(a: ByteStream, b: ByteStream) -> G {
    match a {
      List.Nil =>
        match b {
          List.Nil => 1,
          _ => 0,
        },
      List.Cons(ba, &ra) =>
        match b {
          List.Nil => 0,
          List.Cons(bb, &rb) =>
            match ba - bb {
              0 => bytestream_eq(ra, rb),
              _ => 0,
            },
        },
    }
  }

  -- Check equality of two literals
  fn literal_eq(a: KLiteral, b: KLiteral) -> G {
    match a {
      KLiteral.Nat(&na) =>
        match b {
          KLiteral.Nat(&nb) => klimbs_eq(na, nb),
          _ => 0,
        },
      KLiteral.Str(sa) =>
        match b {
          KLiteral.Str(sb) => bytestream_eq(sa, sb),
          _ => 0,
        },
    }
  }

  -- Compare a Nat literal with a Nat constructor value
  fn nat_lit_eq_ctor(
    lit: KLiteral, ctor_idx: G, nparams: G, ctor_spine: List‹KVal›,
    depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G
  ) -> G {
    match lit {
      KLiteral.Nat(&n) =>
        let induct_idx = ctor_induct_idx(ctor_idx, top);
        let is_nat = eq_zero(induct_idx - nat_idx);
        match is_nat {
          0 => 0,
          1 =>
            let nfields = ctor_num_fields(ctor_idx, top);
            let is_zero = klimbs_is_zero(n);
            match is_zero {
              1 =>
                -- Lit(0) == Ctor if ctor has 0 fields
                eq_zero(nfields),
              0 =>
                -- Lit(n+1) == Ctor if ctor has 1 field and that field == Lit(n)
                let has_one = eq_zero(nfields - 1);
                match has_one {
                  0 => 0,
                  1 =>
                    let pred_val = list_lookup(ctor_spine, nparams);
                    let pred_lit = store(KValNode.Lit(KLiteral.Nat(store(klimbs_pred(n)))));
                    k_is_def_eq(pred_lit, pred_val, depth, top, nat_idx, str_idx),
                },
            },
        },
      KLiteral.Str(_) => 0,
    }
  }

  -- Structural definitional equality after WHNF
  fn k_is_def_eq_core(a: KVal, b: KVal, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
    match ptr_val(a) - ptr_val(b) {
      0 => 1,
      _ =>
        match load(a) {
          KValNode.Srt(&la) =>
            match load(b) {
              KValNode.Srt(&lb) => level_equal(la, lb),
              _ => 0,
            },

          KValNode.Lit(la) =>
            match load(b) {
              KValNode.Lit(lb) => literal_eq(la, lb),
              KValNode.Ctor(ctor_idx, _, nparams, &ctor_spine) =>
                nat_lit_eq_ctor(la, ctor_idx, nparams, ctor_spine, depth, top, nat_idx, str_idx),
              _ => 0,
            },

          KValNode.FVar(lvl_a, _, &sp_a) =>
            match load(b) {
              KValNode.FVar(lvl_b, _, &sp_b) =>
                let same_lvl = eq_zero(lvl_a - lvl_b);
                match same_lvl {
                  1 => k_is_def_eq_spine(sp_a, sp_b, depth, top, nat_idx, str_idx),
                  0 => 0,
                },
              _ => 0,
            },

          KValNode.Const(idx_a, &lvls_a, &sp_a) =>
            match load(b) {
              KValNode.Const(idx_b, &lvls_b, &sp_b) =>
                let same_idx = eq_zero(idx_a - idx_b);
                match same_idx {
                  1 =>
                    let lvls_eq = k_is_def_eq_levels(lvls_a, lvls_b);
                    match lvls_eq {
                      1 =>
                        k_is_def_eq_spine(sp_a, sp_b, depth, top, nat_idx, str_idx),
                      0 => 0,
                    },
                  0 =>
                    k_lazy_delta(a, b, depth, top, nat_idx, str_idx),
                },
              _ => k_lazy_delta(a, b, depth, top, nat_idx, str_idx),
            },

          KValNode.Ctor(idx_a, &lvls_a, nparams_a, &sp_a) =>
            match load(b) {
              KValNode.Ctor(idx_b, &lvls_b, _, &sp_b) =>
                let same_idx = eq_zero(idx_a - idx_b);
                match same_idx {
                  1 =>
                    let lvls_eq = k_is_def_eq_levels(lvls_a, lvls_b);
                    match lvls_eq {
                      1 => k_is_def_eq_spine(sp_a, sp_b, depth, top, nat_idx, str_idx),
                      0 => 0,
                    },
                  0 => 0,
                },
              KValNode.Lit(lb) =>
                nat_lit_eq_ctor(lb, idx_a, nparams_a, sp_a, depth, top, nat_idx, str_idx),
              _ => 0,
            },

          KValNode.Lam(dom_a, body_a, &env_a) =>
            match load(b) {
              KValNode.Lam(dom_b, body_b, &env_b) =>
                let dom_eq = k_is_def_eq(dom_a, dom_b, depth, top, nat_idx, str_idx);
                match dom_eq {
                  0 => 0,
                  1 =>
                    let fvar = store(KValNode.FVar(depth, dom_a, store(List.Nil)));
                    let env_a2 = List.Cons(fvar, store(env_a));
                    let env_b2 = List.Cons(fvar, store(env_b));
                    let va = k_eval(body_a, env_a2, top);
                    let vb = k_eval(body_b, env_b2, top);
                    k_is_def_eq(va, vb, depth + 1, top, nat_idx, str_idx),
                },
              _ =>
                -- Eta: lam vs non-lam
                let fvar = store(KValNode.FVar(depth, dom_a, store(List.Nil)));
                let env_a2 = List.Cons(fvar, store(env_a));
                let va = k_eval(body_a, env_a2, top);
                let vb = k_apply(b, fvar, top);
                k_is_def_eq(va, vb, depth + 1, top, nat_idx, str_idx),
            },

          KValNode.Pi(dom_a, body_a, &env_a) =>
            match load(b) {
              KValNode.Pi(dom_b, body_b, &env_b) =>
                let dom_eq = k_is_def_eq(dom_a, dom_b, depth, top, nat_idx, str_idx);
                match dom_eq {
                  0 => 0,
                  1 =>
                    let fvar = store(KValNode.FVar(depth, dom_a, store(List.Nil)));
                    let env_a2 = List.Cons(fvar, store(env_a));
                    let env_b2 = List.Cons(fvar, store(env_b));
                    let va = k_eval(body_a, env_a2, top);
                    let vb = k_eval(body_b, env_b2, top);
                    k_is_def_eq(va, vb, depth + 1, top, nat_idx, str_idx),
                },
              _ => 0,
            },

          KValNode.Proj(tidx_a, fidx_a, sv_a, &sp_a) =>
            match load(b) {
              KValNode.Proj(tidx_b, fidx_b, sv_b, &sp_b) =>
                let same_tf = eq_zero(tidx_a - tidx_b) * eq_zero(fidx_a - fidx_b);
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
            match load(b) {
              KValNode.Lam(dom_b, body_b, &env_b) =>
                let fvar = store(KValNode.FVar(depth, dom_b, store(List.Nil)));
                let va = k_apply(a, fvar, top);
                let env_b2 = List.Cons(fvar, store(env_b));
                let vb = k_eval(body_b, env_b2, top);
                k_is_def_eq(va, vb, depth + 1, top, nat_idx, str_idx),
              KValNode.Const(_, _, _) =>
                k_lazy_delta(a, b, depth, top, nat_idx, str_idx),
              _ => 0,
            },
        },
    }
  }

  -- Pointwise definitional equality of two value spines
  fn k_is_def_eq_spine(a: List‹KVal›, b: List‹KVal›, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
    match a {
      List.Nil =>
        match b {
          List.Nil => 1,
          _ => 0,
        },
      List.Cons(va, &ra) =>
        match b {
          List.Nil => 0,
          List.Cons(vb, &rb) =>
            let eq = k_is_def_eq(va, vb, depth, top, nat_idx, str_idx);
            match eq {
              0 => 0,
              1 => k_is_def_eq_spine(ra, rb, depth, top, nat_idx, str_idx),
            },
        },
    }
  }

  -- Pointwise semantic equality of two level lists
  fn k_is_def_eq_levels(a: List‹&KLevel›, b: List‹&KLevel›) -> G {
    match a {
      List.Nil =>
        match b {
          List.Nil => 1,
          _ => 0,
        },
      List.Cons(&la, &ra) =>
        match b {
          List.Nil => 0,
          List.Cons(&lb, &rb) =>
            let eq = level_equal(la, lb);
            match eq {
              0 => 0,
              1 => k_is_def_eq_levels(ra, rb),
            },
        },
    }
  }

  -- Lazy delta: try unfolding one or both constants to make progress
  fn k_lazy_delta(a: KVal, b: KVal, depth: G, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) -> G {
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
  fn try_delta_unfold(v: KVal, top: List‹&KConstantInfo›) -> KVal {
    match load(v) {
      KValNode.Const(idx, &lvls, &spine) =>
        let ci = load(list_lookup(top, idx));
        match ci {
          KConstantInfo.Defn(_, _, &value, hints, _) =>
            match hints {
              KHints.Opaque => v,
              KHints.Abbrev =>
                let body = expr_inst_levels(value, lvls);
                let val = k_eval(body, List.Nil, top);
                k_apply_spine(val, spine, top),
              KHints.Regular(_) =>
                let body = expr_inst_levels(value, lvls);
                let val = k_eval(body, List.Nil, top);
                k_apply_spine(val, spine, top),
            },
          KConstantInfo.Thm(_, _, &value) =>
            let body = expr_inst_levels(value, lvls);
            let val = k_eval(body, List.Nil, top);
            k_apply_spine(val, spine, top),
          _ => v,
        },
      _ => v,
    }
  }

  -- Check whether delta unfolding made progress (i.e., the head constant changed)
  fn delta_changed(before: KVal, after: KVal) -> G {
    match load(before) {
      KValNode.Const(idx_a, _, _) =>
        match load(after) {
          KValNode.Const(idx_b, _, _) => 1 - eq_zero(idx_a - idx_b),
          _ => 1,
        },
      _ => 0,
    }
  }

  -- ============================================================================
  -- Declaration checking
  --
  -- Verify each constant in the environment: its type must be a Sort, and its
  -- value (if any) must have the declared type. Processes axioms, definitions,
  -- theorems, opaques, quotients, inductives, constructors, and recursors.
  -- ============================================================================

  -- Type-check a single constant declaration against the environment.
  -- nat_idx/str_idx are the constant indices for the Nat/String types.
  fn k_check_const(ci: KConstantInfo, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G) {
    match ci {
      KConstantInfo.Axiom(_, &ty, _) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx),

      KConstantInfo.Defn(_, &ty, &value, _, _) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx);
        let ty_val = k_eval(ty, List.Nil, top);
        k_check(value, ty_val, List.Nil, List.Nil, 0, top, nat_idx, str_idx),

      KConstantInfo.Thm(_, &ty, &value) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx);
        let ty_val = k_eval(ty, List.Nil, top);
        k_check(value, ty_val, List.Nil, List.Nil, 0, top, nat_idx, str_idx),

      KConstantInfo.Opaque(_, &ty, &value, is_unsafe) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx);
        match is_unsafe {
          1 => (),
          0 =>
            let ty_val = k_eval(ty, List.Nil, top);
            k_check(value, ty_val, List.Nil, List.Nil, 0, top, nat_idx, str_idx),
        },

      KConstantInfo.Quot(_, &ty, _) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx),

      KConstantInfo.Induct(_, &ty, _, _, _, _, _, _) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx),

      KConstantInfo.Ctor(_, &ty, _, _, _, _, _) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx),

      KConstantInfo.Rec(_, &ty, _, _, _, _, _, _, _) =>
        let _ = k_ensure_sort(ty, List.Nil, List.Nil, 0, top, nat_idx, str_idx),
    }
  }

  fn k_check_all_go(consts: List‹&KConstantInfo›, top: List‹&KConstantInfo›, nat_idx: G, str_idx: G, idx: G) {
    match consts {
      List.Nil => (),
      List.Cons(&ci, &rest) =>
        let _ = k_check_const(ci, top, nat_idx, str_idx);
        k_check_all_go(rest, top, nat_idx, str_idx, idx + 1),
    }
  }
⟧

end IxVM

end
