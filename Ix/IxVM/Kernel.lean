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
      KValEnv.VECons(&v, &rest) =>
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
      KValList.VLCons(&v, &rest) =>
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
      KValList.VLNil => KValList.VLCons(store(v), store(KValList.VLNil)),
      KValList.VLCons(&head, &rest) =>
        KValList.VLCons(store(head), store(val_list_snoc(rest, v))),
    }
  }

  -- Compute the length of a value list
  fn val_list_length(list: KValList) -> [G; 8] {
    match list {
      KValList.VLNil => [0; 8],
      KValList.VLCons(_, &rest) => relaxed_u64_succ(val_list_length(rest)),
    }
  }

  -- Look up a level in a level list by index
  fn level_list_lookup(list: KLevelList, idx: [G; 8]) -> KLevel {
    match list {
      KLevelList.LLCons(&l, &rest) =>
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
      KConstList.CLCons(&ci, &rest) =>
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
      KRecRuleList.RRCons(&rule, &rest) =>
        match rule {
          KRecRule.RRMk(idx, nf, &rhs) =>
            let found = u64_eq(idx, ctor_idx);
            match found {
              1 => KRecRule.RRMk(idx, nf, store(rhs)),
              0 => rec_rule_find(rest, ctor_idx),
            },
        },
    }
  }

  -- ============================================================================
  -- Constant info accessors
  -- ============================================================================

  -- Extract the type expression from any constant info variant
  fn const_type(ci: KConstantInfo) -> KExpr {
    match ci {
      KConstantInfo.CIAxiom(_, &ty, _) => ty,
      KConstantInfo.CIDefn(_, &ty, _, _, _) => ty,
      KConstantInfo.CIThm(_, &ty, _) => ty,
      KConstantInfo.CIOpaque(_, &ty, _, _) => ty,
      KConstantInfo.CIQuot(_, &ty, _) => ty,
      KConstantInfo.CIInduct(_, &ty, _, _, _, _, _, _) => ty,
      KConstantInfo.CICtor(_, &ty, _, _, _, _, _) => ty,
      KConstantInfo.CIRec(_, &ty, _, _, _, _, _, _, _) => ty,
    }
  }

  -- Extract the number of universe level parameters from any constant info variant
  fn const_num_levels(ci: KConstantInfo) -> [G; 8] {
    match ci {
      KConstantInfo.CIAxiom(n, _, _) => n,
      KConstantInfo.CIDefn(n, _, _, _, _) => n,
      KConstantInfo.CIThm(n, _, _) => n,
      KConstantInfo.CIOpaque(n, _, _, _) => n,
      KConstantInfo.CIQuot(n, _, _) => n,
      KConstantInfo.CIInduct(n, _, _, _, _, _, _, _) => n,
      KConstantInfo.CICtor(n, _, _, _, _, _, _) => n,
      KConstantInfo.CIRec(n, _, _, _, _, _, _, _, _) => n,
    }
  }

  -- ============================================================================
  -- Level operations
  -- ============================================================================

  -- Check if a level is definitely not zero (sound approximation)
  fn level_is_not_zero(l: KLevel) -> G {
    match l {
      KLevel.LZero => 0,
      KLevel.LParam(_) => 0,
      KLevel.LSucc(_) => 1,
      KLevel.LMax(&a, &b) => match (level_is_not_zero(a), level_is_not_zero(b)) {
        (0, 0) => 0,
        _ => 1,
      },
      KLevel.LIMax(_, &b) => level_is_not_zero(b),
    }
  }

  -- Structural equality of levels (after reduction)
  fn level_eq(a: KLevel, b: KLevel) -> G {
    match a {
      KLevel.LZero =>
        match b {
          KLevel.LZero => 1,
          _ => 0,
        },
      KLevel.LSucc(&a1) =>
        match b {
          KLevel.LSucc(&b1) => level_eq(a1, b1),
          _ => 0,
        },
      KLevel.LMax(&a1, &a2) =>
        match b {
          KLevel.LMax(&b1, &b2) => level_eq(a1, b1) * level_eq(a2, b2),
          _ => 0,
        },
      KLevel.LIMax(&a1, &a2) =>
        match b {
          KLevel.LIMax(&b1, &b2) => level_eq(a1, b1) * level_eq(a2, b2),
          _ => 0,
        },
      KLevel.LParam(i) =>
        match b {
          KLevel.LParam(j) => u64_eq(i, j),
          _ => 0,
        },
    }
  }

  -- level_leq: check a <= b (heuristic, sound but incomplete)
  fn level_leq(a: KLevel, b: KLevel) -> G {
    match a {
      KLevel.LZero => 1,
      KLevel.LSucc(&a1) =>
        match b {
          KLevel.LSucc(&b1) => level_leq(a1, b1),
          _ => 0,
        },
      KLevel.LParam(i) =>
        match b {
          KLevel.LParam(j) => u64_eq(i, j),
          _ => 0,
        },
      KLevel.LMax(&a1, &a2) =>
        level_leq(a1, b) * level_leq(a2, b),
      KLevel.LIMax(&a1, &a2) =>
        match b {
          KLevel.LMax(&b1, &b2) =>
            match (level_leq(a, b1), level_leq(a, b2)) {
              (0, 0) => 0,
              _ => 1,
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
      KLevel.LZero => b,
      _ =>
        match b {
          KLevel.LZero => a,
          _ =>
            let eq = level_eq(a, b);
            match eq {
              1 => a,
              0 =>
                match a {
                  KLevel.LSucc(&a1) =>
                    match b {
                      KLevel.LSucc(&b1) => KLevel.LSucc(store(level_max(a1, b1))),
                      _ => KLevel.LMax(store(a), store(b)),
                    },
                  _ => KLevel.LMax(store(a), store(b)),
                },
            },
        },
    }
  }

  -- Reduce imax(a, b) assuming a and b are already reduced
  fn level_imax(a: KLevel, b: KLevel) -> KLevel {
    match b {
      KLevel.LZero => KLevel.LZero,
      KLevel.LSucc(_) => level_max(a, b),
      _ =>
        match a {
          KLevel.LZero => b,
          _ =>
            let eq = level_eq(a, b);
            match eq {
              1 => a,
              0 => KLevel.LIMax(store(a), store(b)),
            },
        },
    }
  }

  -- Reduce a level to normal form
  fn level_reduce(l: KLevel) -> KLevel {
    match l {
      KLevel.LZero => KLevel.LZero,
      KLevel.LParam(i) => KLevel.LParam(i),
      KLevel.LSucc(&u) => KLevel.LSucc(store(level_reduce(u))),
      KLevel.LMax(&a, &b) => level_max(level_reduce(a), level_reduce(b)),
      KLevel.LIMax(&a, &b) => level_imax(level_reduce(a), level_reduce(b)),
    }
  }

  -- Substitute all Level.Param(i) -> params[i] in a level
  fn level_inst_params(l: KLevel, params: KLevelList) -> KLevel {
    match l {
      KLevel.LZero => KLevel.LZero,
      KLevel.LSucc(&u) => KLevel.LSucc(store(level_inst_params(u, params))),
      KLevel.LMax(&a, &b) =>
        level_max(level_inst_params(a, params), level_inst_params(b, params)),
      KLevel.LIMax(&a, &b) =>
        level_imax(level_inst_params(a, params), level_inst_params(b, params)),
      KLevel.LParam(i) => level_list_lookup(params, i),
    }
  }

  -- ============================================================================
  -- Expression-level level substitution
  -- ============================================================================

  -- Substitute all Level.Param(i) -> params[i] in all levels within an expression
  fn expr_inst_levels(e: KExpr, params: KLevelList) -> KExpr {
    match e {
      KExpr.EBVar(i) => KExpr.EBVar(i),
      KExpr.ESort(&l) =>
        KExpr.ESort(store(level_inst_params(l, params))),
      KExpr.EConst(idx, &lvls) =>
        KExpr.EConst(idx, store(level_list_inst(lvls, params))),
      KExpr.EApp(&f, &a) =>
        KExpr.EApp(store(expr_inst_levels(f, params)), store(expr_inst_levels(a, params))),
      KExpr.ELam(&ty, &body) =>
        KExpr.ELam(store(expr_inst_levels(ty, params)), store(expr_inst_levels(body, params))),
      KExpr.EForallE(&ty, &body) =>
        KExpr.EForallE(store(expr_inst_levels(ty, params)), store(expr_inst_levels(body, params))),
      KExpr.ELetE(&ty, &val, &body) =>
        KExpr.ELetE(
          store(expr_inst_levels(ty, params)),
          store(expr_inst_levels(val, params)),
          store(expr_inst_levels(body, params))),
      KExpr.ELit(lit) => KExpr.ELit(lit),
      KExpr.EProj(tidx, fidx, &e1) =>
        KExpr.EProj(tidx, fidx, store(expr_inst_levels(e1, params))),
    }
  }

  -- Substitute level params in a level list
  fn level_list_inst(lvls: KLevelList, params: KLevelList) -> KLevelList {
    match lvls {
      KLevelList.LLNil => KLevelList.LLNil,
      KLevelList.LLCons(&l, &rest) =>
        KLevelList.LLCons(
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
      KExpr.EBVar(idx) =>
        val_env_lookup(env, idx),

      KExpr.ESort(&l) =>
        KVal.VSort(store(level_reduce(l))),

      KExpr.EConst(idx, &lvls) =>
        k_eval_const(idx, lvls, top),

      KExpr.EApp(&f, &a) =>
        let vf = k_eval(f, env, top);
        let va = k_eval(a, env, top);
        k_apply(vf, va, top),

      KExpr.ELam(&ty, &body) =>
        let ty_val = k_eval(ty, env, top);
        KVal.VLam(store(ty_val), store(body), store(env)),

      KExpr.EForallE(&ty, &body) =>
        let ty_val = k_eval(ty, env, top);
        KVal.VPi(store(ty_val), store(body), store(env)),

      KExpr.ELetE(_, &val, &body) =>
        let v = k_eval(val, env, top);
        let env2 = KValEnv.VECons(store(v), store(env));
        k_eval(body, env2, top),

      KExpr.ELit(lit) =>
        KVal.VLit(lit),

      KExpr.EProj(tidx, fidx, &e1) =>
        let v = k_eval(e1, env, top);
        k_eval_proj(tidx, fidx, v),
    }
  }

  -- Evaluate a constant reference
  fn k_eval_const(idx: [G; 8], lvls: KLevelList, top: KConstList) -> KVal {
    let ci = const_list_lookup(top, idx);
    match ci {
      KConstantInfo.CIDefn(_, _, &value, hints, _) =>
        match hints {
          KHints.HOpaque =>
            KVal.VConst(idx, store(lvls), store(KValList.VLNil)),
          KHints.HAbbrev =>
            let body = expr_inst_levels(value, lvls);
            k_eval(body, KValEnv.VENil, top),
          KHints.HRegular(_) =>
            let body = expr_inst_levels(value, lvls);
            k_eval(body, KValEnv.VENil, top),
        },

      KConstantInfo.CICtor(_, _, _, _, nparams, _, _) =>
        KVal.VCtor(idx, store(lvls), nparams, store(KValList.VLNil)),

      -- Theorems, opaques, axioms, recursors, inductives, quotients: irreducible
      _ => KVal.VConst(idx, store(lvls), store(KValList.VLNil)),
    }
  }

  -- Evaluate a projection
  fn k_eval_proj(tidx: [G; 8], fidx: [G; 8], v: KVal) -> KVal {
    match v {
      KVal.VCtor(_, _, nparams, &spine) =>
        let field_idx = u64_add(nparams, fidx);
        val_list_lookup(spine, field_idx),
      _ =>
        KVal.VProj(tidx, fidx, store(v), store(KValList.VLNil)),
    }
  }

  -- Apply a value to an argument
  fn k_apply(f: KVal, arg: KVal, top: KConstList) -> KVal {
    match f {
      KVal.VLam(_, &body, &env) =>
        let env2 = KValEnv.VECons(store(arg), store(env));
        k_eval(body, env2, top),

      KVal.VCtor(idx, &lvls, nparams, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        KVal.VCtor(idx, store(lvls), nparams, store(spine2)),

      KVal.VFVar(lvl, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        KVal.VFVar(lvl, store(spine2)),

      KVal.VConst(idx, &lvls, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        try_iota(idx, lvls, spine2, top),

      KVal.VProj(tidx, fidx, &sv, &spine) =>
        let spine2 = val_list_snoc(spine, arg);
        KVal.VProj(tidx, fidx, store(sv), store(spine2)),
    }
  }

  -- Apply a value to a list of arguments
  fn k_apply_spine(f: KVal, spine: KValList, top: KConstList) -> KVal {
    match spine {
      KValList.VLNil => f,
      KValList.VLCons(&v, &rest) =>
        let f2 = k_apply(f, v, top);
        k_apply_spine(f2, rest, top),
    }
  }

  -- ============================================================================
  -- Iota reduction (recursor on constructor)
  -- ============================================================================

  -- Try iota reduction: if idx refers to a recursor and the major premise is a
  -- constructor, apply the matching recursor rule; otherwise return a neutral VConst
  fn try_iota(idx: [G; 8], lvls: KLevelList, spine: KValList, top: KConstList) -> KVal {
    let ci = const_list_lookup(top, idx);
    match ci {
      KConstantInfo.CIRec(_, _, nparams, nindices, nmotives, nminors, &rules, _, _) =>
        let maj_idx = u64_add(u64_add(u64_add(nparams, nmotives), nminors), nindices);
        let spine_len = val_list_length(spine);
        let not_have_major = u64_is_zero(u64_sub(relaxed_u64_succ(spine_len), relaxed_u64_succ(maj_idx)));
        match not_have_major {
          1 => KVal.VConst(idx, store(lvls), store(spine)),
          0 =>
            let major = val_list_lookup(spine, maj_idx);
            match major {
              KVal.VCtor(ctor_idx, _, ctor_nparams, &ctor_spine) =>
                let rule = rec_rule_find(rules, ctor_idx);
                match rule {
                  KRecRule.RRMk(_, nfields, &rhs) =>
                    let rhs_inst = expr_inst_levels(rhs, lvls);
                    let rhs_val = k_eval(rhs_inst, KValEnv.VENil, top);
                    let params_motives_minors = val_list_take(spine, u64_add(u64_add(nparams, nmotives), nminors));
                    let result = k_apply_spine(rhs_val, params_motives_minors, top);
                    let fields = val_list_drop(ctor_spine, ctor_nparams);
                    let result2 = k_apply_spine(result, fields, top);
                    let remaining = val_list_drop(spine, relaxed_u64_succ(maj_idx));
                    k_apply_spine(result2, remaining, top),
                },
              _ =>
                KVal.VConst(idx, store(lvls), store(spine)),
            },
        },

      _ => KVal.VConst(idx, store(lvls), store(spine)),
    }
  }

  -- Take the first n elements of a val list
  fn val_list_take(list: KValList, n: [G; 8]) -> KValList {
    let z = u64_is_zero(n);
    match z {
      1 => KValList.VLNil,
      0 =>
        match list {
          KValList.VLCons(&v, &rest) =>
            KValList.VLCons(store(v), store(val_list_take(rest, relaxed_u64_pred(n)))),
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
          KValList.VLCons(_, &rest) =>
            val_list_drop(rest, relaxed_u64_pred(n)),
        },
    }
  }

  -- ============================================================================
  -- WHNF (additional reductions beyond eval)
  -- ============================================================================

  -- Reduce a value to Weak Head Normal Form by retrying projection and iota reductions
  fn k_whnf(v: KVal, top: KConstList) -> KVal {
    match v {
      KVal.VProj(tidx, fidx, &sv, &spine) =>
        let sv2 = k_whnf(sv, top);
        match sv2 {
          KVal.VCtor(_, _, nparams, &ctor_spine) =>
            let field_idx = u64_add(nparams, fidx);
            let field = val_list_lookup(ctor_spine, field_idx);
            let result = k_apply_spine(field, spine, top);
            k_whnf(result, top),
          _ =>
            KVal.VProj(tidx, fidx, store(sv2), store(spine)),
        },

      KVal.VConst(idx, &lvls, &spine) =>
        let result = try_iota(idx, lvls, spine, top);
        match result {
          KVal.VConst(idx2, _, _) =>
            let same = u64_eq(idx, idx2);
            match same {
              1 => result,
              0 => k_whnf(result, top),
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
      KVal.VSort(&l) => KExpr.ESort(store(l)),

      KVal.VLit(lit) => KExpr.ELit(lit),

      KVal.VLam(&dom, &body, &env) =>
        let dom_expr = k_quote(dom, depth, top);
        let fvar = KVal.VFVar(depth, store(KValList.VLNil));
        let env2 = KValEnv.VECons(store(fvar), store(env));
        let body_val = k_eval(body, env2, top);
        let body_expr = k_quote(body_val, relaxed_u64_succ(depth), top);
        KExpr.ELam(store(dom_expr), store(body_expr)),

      KVal.VPi(&dom, &body, &env) =>
        let dom_expr = k_quote(dom, depth, top);
        let fvar = KVal.VFVar(depth, store(KValList.VLNil));
        let env2 = KValEnv.VECons(store(fvar), store(env));
        let body_val = k_eval(body, env2, top);
        let body_expr = k_quote(body_val, relaxed_u64_succ(depth), top);
        KExpr.EForallE(store(dom_expr), store(body_expr)),

      KVal.VCtor(idx, &lvls, _, &spine) =>
        let base = KExpr.EConst(idx, store(lvls));
        quote_spine(base, spine, depth, top),

      KVal.VFVar(lvl, &spine) =>
        let idx = u64_sub(relaxed_u64_pred(depth), lvl);
        let base = KExpr.EBVar(idx);
        quote_spine(base, spine, depth, top),

      KVal.VConst(idx, &lvls, &spine) =>
        let base = KExpr.EConst(idx, store(lvls));
        quote_spine(base, spine, depth, top),

      KVal.VProj(tidx, fidx, &sv, &spine) =>
        let sv_expr = k_quote(sv, depth, top);
        let base = KExpr.EProj(tidx, fidx, store(sv_expr));
        quote_spine(base, spine, depth, top),
    }
  }

  -- Quote a spine of arguments, wrapping each in an EApp around the base expression
  fn quote_spine(base: KExpr, spine: KValList, depth: [G; 8], top: KConstList) -> KExpr {
    match spine {
      KValList.VLNil => base,
      KValList.VLCons(&v, &rest) =>
        let arg_expr = k_quote(v, depth, top);
        let app = KExpr.EApp(store(base), store(arg_expr));
        quote_spine(app, rest, depth, top),
    }
  }

  -- ============================================================================
  -- Type inference
  -- ============================================================================

  -- Infer the type of an expression under the given type and value environments
  fn k_infer(e: KExpr, types: KValList, env: KValEnv, depth: [G; 8], top: KConstList) -> KVal {
    match e {
      KExpr.EBVar(idx) =>
        val_list_lookup(types, idx),

      KExpr.ESort(&l) =>
        KVal.VSort(store(KLevel.LSucc(store(l)))),

      KExpr.ELit(lit) =>
        match lit {
          -- TODO: need primitive type addresses for Nat and String
          KLiteral.LitNat(_) =>
            KVal.VSort(store(KLevel.LSucc(store(KLevel.LZero)))),
          KLiteral.LitStr(_) =>
            KVal.VSort(store(KLevel.LSucc(store(KLevel.LZero)))),
        },

      KExpr.EConst(idx, &lvls) =>
        let ci = const_list_lookup(top, idx);
        let expected = const_num_levels(ci);
        let given = level_list_length(lvls);
        assert_eq!(u64_eq(expected, given), 1);
        let ty = const_type(ci);
        let ty_inst = expr_inst_levels(ty, lvls);
        k_eval(ty_inst, KValEnv.VENil, top),

      KExpr.EApp(&f, &a) =>
        let fn_type = k_infer(f, types, env, depth, top);
        let fn_type_whnf = k_whnf(fn_type, top);
        match fn_type_whnf {
          KVal.VPi(&dom, &body, &pi_env) =>
            let arg_type = k_infer(a, types, env, depth, top);
            assert_eq!(k_is_def_eq(arg_type, dom, depth, top), 1);
            let arg_val = k_eval(a, env, top);
            let pi_env2 = KValEnv.VECons(store(arg_val), store(pi_env));
            k_eval(body, pi_env2, top),
        },

      KExpr.ELam(&ty, &body) =>
        let _x = k_ensure_sort(ty, types, env, depth, top);
        let dom_val = k_eval(ty, env, top);
        let fvar = KVal.VFVar(depth, store(KValList.VLNil));
        let types2 = KValList.VLCons(store(dom_val), store(types));
        let env2 = KValEnv.VECons(store(fvar), store(env));
        let body_type = k_infer(body, types2, env2, relaxed_u64_succ(depth), top);
        let body_type_expr = k_quote(body_type, relaxed_u64_succ(depth), top);
        KVal.VPi(store(dom_val), store(body_type_expr), store(env)),

      KExpr.EForallE(&ty, &body) =>
        let dom_level = k_ensure_sort(ty, types, env, depth, top);
        let dom_val = k_eval(ty, env, top);
        let fvar = KVal.VFVar(depth, store(KValList.VLNil));
        let types2 = KValList.VLCons(store(dom_val), store(types));
        let env2 = KValEnv.VECons(store(fvar), store(env));
        let body_level = k_ensure_sort(body, types2, env2, relaxed_u64_succ(depth), top);
        let result_level = level_imax(dom_level, body_level);
        KVal.VSort(store(result_level)),

      KExpr.ELetE(&ty, &val, &body) =>
        let _x = k_ensure_sort(ty, types, env, depth, top);
        let ty_val = k_eval(ty, env, top);
        let val_type = k_infer(val, types, env, depth, top);
        assert_eq!(k_is_def_eq(val_type, ty_val, depth, top), 1);
        let val_val = k_eval(val, env, top);
        let types2 = KValList.VLCons(store(ty_val), store(types));
        let env2 = KValEnv.VECons(store(val_val), store(env));
        k_infer(body, types2, env2, relaxed_u64_succ(depth), top),

      KExpr.EProj(tidx, fidx, &e1) =>
        -- TODO: properly compute projection type from inductive info
        let struct_type = k_infer(e1, types, env, depth, top);
        let struct_type_whnf = k_whnf(struct_type, top);
        let struct_val = k_eval(e1, env, top);
        let proj_val = k_eval_proj(tidx, fidx, struct_val);
        KVal.VSort(store(KLevel.LZero)),
    }
  }

  -- Ensure a type expression evaluates to a Sort, returning the level
  fn k_ensure_sort(e: KExpr, types: KValList, env: KValEnv, depth: [G; 8], top: KConstList) -> KLevel {
    let ty = k_infer(e, types, env, depth, top);
    let ty_whnf = k_whnf(ty, top);
    match ty_whnf {
      KVal.VSort(&l) => l,
    }
  }

  -- Compute the length of a level list
  fn level_list_length(list: KLevelList) -> [G; 8] {
    match list {
      KLevelList.LLNil => [0; 8],
      KLevelList.LLCons(_, &rest) => relaxed_u64_succ(level_list_length(rest)),
    }
  }

  -- ============================================================================
  -- Definitional equality
  -- ============================================================================

  -- Check definitional equality of two values: first try a quick syntactic check,
  -- then reduce to WHNF and compare structurally
  fn k_is_def_eq(a: KVal, b: KVal, depth: [G; 8], top: KConstList) -> G {
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
            -- TODO: proof irrelevance check
            k_is_def_eq_core(a_whnf, b_whnf, depth, top),
        },
    }
  }

  -- Quick syntactic check for definitional equality (sorts and literals only)
  fn k_quick_def_eq(a: KVal, b: KVal) -> G {
    match a {
      KVal.VSort(&la) =>
        match b {
          KVal.VSort(&lb) => level_equal(la, lb),
          _ => 0,
        },
      KVal.VLit(la) =>
        match b {
          KVal.VLit(lb) => literal_eq(la, lb),
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Check equality of two literals (nat or string, compared by their u64 values)
  fn literal_eq(a: KLiteral, b: KLiteral) -> G {
    match a {
      KLiteral.LitNat(na) =>
        match b {
          KLiteral.LitNat(nb) => u64_eq(na, nb),
          _ => 0,
        },
      KLiteral.LitStr(sa) =>
        match b {
          KLiteral.LitStr(sb) => u64_eq(sa, sb),
          _ => 0,
        },
    }
  }

  -- Structural definitional equality after WHNF
  fn k_is_def_eq_core(a: KVal, b: KVal, depth: [G; 8], top: KConstList) -> G {
    match a {
      KVal.VSort(&la) =>
        match b {
          KVal.VSort(&lb) => level_equal(la, lb),
          _ => 0,
        },

      KVal.VLit(la) =>
        match b {
          KVal.VLit(lb) => literal_eq(la, lb),
          _ => 0,
        },

      KVal.VFVar(lvl_a, &sp_a) =>
        match b {
          KVal.VFVar(lvl_b, &sp_b) =>
            let same_lvl = u64_eq(lvl_a, lvl_b);
            match same_lvl {
              1 => k_is_def_eq_spine(sp_a, sp_b, depth, top),
              0 => 0,
            },
          _ => 0,
        },

      KVal.VConst(idx_a, &lvls_a, &sp_a) =>
        match b {
          KVal.VConst(idx_b, &lvls_b, &sp_b) =>
            let same_idx = u64_eq(idx_a, idx_b);
            match same_idx {
              1 =>
                let lvls_eq = k_is_def_eq_levels(lvls_a, lvls_b);
                match lvls_eq {
                  1 => k_is_def_eq_spine(sp_a, sp_b, depth, top),
                  0 => 0,
                },
              0 =>
                k_lazy_delta(a, b, depth, top),
            },
          _ => k_lazy_delta(a, b, depth, top),
        },

      KVal.VCtor(idx_a, &lvls_a, _, &sp_a) =>
        match b {
          KVal.VCtor(idx_b, &lvls_b, _, &sp_b) =>
            let same_idx = u64_eq(idx_a, idx_b);
            match same_idx {
              1 =>
                let lvls_eq = k_is_def_eq_levels(lvls_a, lvls_b);
                match lvls_eq {
                  1 => k_is_def_eq_spine(sp_a, sp_b, depth, top),
                  0 => 0,
                },
              0 => 0,
            },
          _ => 0,
        },

      KVal.VLam(&dom_a, &body_a, &env_a) =>
        match b {
          KVal.VLam(&dom_b, &body_b, &env_b) =>
            let dom_eq = k_is_def_eq(dom_a, dom_b, depth, top);
            match dom_eq {
              0 => 0,
              1 =>
                let fvar = KVal.VFVar(depth, store(KValList.VLNil));
                let env_a2 = KValEnv.VECons(store(fvar), store(env_a));
                let env_b2 = KValEnv.VECons(store(fvar), store(env_b));
                let va = k_eval(body_a, env_a2, top);
                let vb = k_eval(body_b, env_b2, top);
                k_is_def_eq(va, vb, relaxed_u64_succ(depth), top),
            },
          _ =>
            -- Eta: lam vs non-lam
            let fvar = KVal.VFVar(depth, store(KValList.VLNil));
            let env_a2 = KValEnv.VECons(store(fvar), store(env_a));
            let va = k_eval(body_a, env_a2, top);
            let vb = k_apply(b, fvar, top);
            k_is_def_eq(va, vb, relaxed_u64_succ(depth), top),
        },

      KVal.VPi(&dom_a, &body_a, &env_a) =>
        match b {
          KVal.VPi(&dom_b, &body_b, &env_b) =>
            let dom_eq = k_is_def_eq(dom_a, dom_b, depth, top);
            match dom_eq {
              0 => 0,
              1 =>
                let fvar = KVal.VFVar(depth, store(KValList.VLNil));
                let env_a2 = KValEnv.VECons(store(fvar), store(env_a));
                let env_b2 = KValEnv.VECons(store(fvar), store(env_b));
                let va = k_eval(body_a, env_a2, top);
                let vb = k_eval(body_b, env_b2, top);
                k_is_def_eq(va, vb, relaxed_u64_succ(depth), top),
            },
          _ => 0,
        },

      KVal.VProj(tidx_a, fidx_a, &sv_a, &sp_a) =>
        match b {
          KVal.VProj(tidx_b, fidx_b, &sv_b, &sp_b) =>
            let same_tf = u64_eq(tidx_a, tidx_b) * u64_eq(fidx_a, fidx_b);
            match same_tf {
              1 =>
                let sv_eq = k_is_def_eq(sv_a, sv_b, depth, top);
                match sv_eq {
                  1 => k_is_def_eq_spine(sp_a, sp_b, depth, top),
                  0 => 0,
                },
              0 => 0,
            },
          _ => 0,
        },

      -- Eta: non-lam vs lam (symmetric case)
      _ =>
        match b {
          KVal.VLam(&dom_b, &body_b, &env_b) =>
            let fvar = KVal.VFVar(depth, store(KValList.VLNil));
            let va = k_apply(a, fvar, top);
            let env_b2 = KValEnv.VECons(store(fvar), store(env_b));
            let vb = k_eval(body_b, env_b2, top);
            k_is_def_eq(va, vb, relaxed_u64_succ(depth), top),
          KVal.VConst(_, _, _) =>
            k_lazy_delta(a, b, depth, top),
          _ => 0,
        },
    }
  }

  -- Pointwise definitional equality of two value spines
  fn k_is_def_eq_spine(a: KValList, b: KValList, depth: [G; 8], top: KConstList) -> G {
    match a {
      KValList.VLNil =>
        match b {
          KValList.VLNil => 1,
          _ => 0,
        },
      KValList.VLCons(&va, &ra) =>
        match b {
          KValList.VLNil => 0,
          KValList.VLCons(&vb, &rb) =>
            let eq = k_is_def_eq(va, vb, depth, top);
            match eq {
              0 => 0,
              1 => k_is_def_eq_spine(ra, rb, depth, top),
            },
        },
    }
  }

  -- Pointwise semantic equality of two level lists
  fn k_is_def_eq_levels(a: KLevelList, b: KLevelList) -> G {
    match a {
      KLevelList.LLNil =>
        match b {
          KLevelList.LLNil => 1,
          _ => 0,
        },
      KLevelList.LLCons(&la, &ra) =>
        match b {
          KLevelList.LLNil => 0,
          KLevelList.LLCons(&lb, &rb) =>
            let eq = level_equal(la, lb);
            match eq {
              0 => 0,
              1 => k_is_def_eq_levels(ra, rb),
            },
        },
    }
  }

  -- Lazy delta: try unfolding one or both constants to make progress
  fn k_lazy_delta(a: KVal, b: KVal, depth: [G; 8], top: KConstList) -> G {
    let a_unfolded = try_delta_unfold(a, top);
    let b_unfolded = try_delta_unfold(b, top);
    let a_changed = delta_changed(a, a_unfolded);
    let b_changed = delta_changed(b, b_unfolded);
    match (a_changed, b_changed) {
      (0, 0) => 0,
      _ => k_is_def_eq(a_unfolded, b_unfolded, depth, top),
    }
  }

  -- Try to delta-unfold a VConst value by looking up its definition and evaluating it;
  -- returns the original value if it is opaque or not a definition
  fn try_delta_unfold(v: KVal, top: KConstList) -> KVal {
    match v {
      KVal.VConst(idx, &lvls, &spine) =>
        let ci = const_list_lookup(top, idx);
        match ci {
          KConstantInfo.CIDefn(_, _, &value, hints, _) =>
            match hints {
              KHints.HOpaque => v,
              KHints.HAbbrev =>
                let body = expr_inst_levels(value, lvls);
                let val = k_eval(body, KValEnv.VENil, top);
                k_apply_spine(val, spine, top),
              KHints.HRegular(_) =>
                let body = expr_inst_levels(value, lvls);
                let val = k_eval(body, KValEnv.VENil, top);
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
      KVal.VConst(idx_a, _, _) =>
        match after {
          KVal.VConst(idx_b, _, _) => 1 - u64_eq(idx_a, idx_b),
          _ => 1,
        },
      _ => 0,
    }
  }

  -- ============================================================================
  -- Declaration checking
  -- ============================================================================

  -- Type-check a single constant declaration against the environment
  fn k_check_const(ci: KConstantInfo, top: KConstList) -> G {
    match ci {
      KConstantInfo.CIAxiom(_, &ty, _) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        1,

      KConstantInfo.CIDefn(_, &ty, &value, _, _) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        let ty_val = k_eval(ty, KValEnv.VENil, top);
        let val_type = k_infer(value, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        assert_eq!(k_is_def_eq(val_type, ty_val, [0; 8], top), 1);
        1,

      KConstantInfo.CIThm(_, &ty, &value) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        let ty_val = k_eval(ty, KValEnv.VENil, top);
        let val_type = k_infer(value, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        assert_eq!(k_is_def_eq(val_type, ty_val, [0; 8], top), 1);
        1,

      KConstantInfo.CIOpaque(_, &ty, &value, _) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        let ty_val = k_eval(ty, KValEnv.VENil, top);
        let val_type = k_infer(value, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        assert_eq!(k_is_def_eq(val_type, ty_val, [0; 8], top), 1);
        1,

      KConstantInfo.CIQuot(_, &ty, _) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        1,

      -- TODO: full inductive validation (positivity, constructor types, etc.)
      KConstantInfo.CIInduct(_, &ty, _, _, _, _, _, _) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        1,

      -- TODO: validate constructor type matches inductive
      KConstantInfo.CICtor(_, &ty, _, _, _, _, _) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        1,

      -- TODO: validate recursor rules, K-flag, etc.
      KConstantInfo.CIRec(_, &ty, _, _, _, _, _, _, _) =>
        let _x = k_ensure_sort(ty, KValList.VLNil, KValEnv.VENil, [0; 8], top);
        1,
    }
  }

  -- Type-check all constants in a list against the environment
  fn k_check_all(consts: KConstList, top: KConstList) -> G {
    match consts {
      KConstList.CLNil => 1,
      KConstList.CLCons(&ci, &rest) =>
        let _x = k_check_const(ci, top);
        k_check_all(rest, top),
    }
  }
⟧

end IxVM

end
