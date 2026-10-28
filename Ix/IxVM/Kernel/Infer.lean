module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Levels
public import Ix.IxVM.Kernel.Whnf
public import Ix.IxVM.Kernel.DefEq
public import Ix.IxVM.Ingress

public section

namespace IxVM

/-! ## Infer — type synthesis with checking

Handles every KExpr node: Sort, BVar, Const, App, Lam, Forall, Let, Lit,
and Proj. Unlike `InferOnly`, this performs the inner validations as it
goes — argument types are checked against domains, binder types are
ensured to be sorts, and projections are checked against their structure.
-/

def infer := ⟦
  -- Context lookup with lift
  -- types[i] is the type of the i-th binder from the innermost. When we
  -- look up BVar(i), we get types[i] but it was assembled at depth d-i-1
  -- (counting from outermost). The current context is at depth d, so we
  -- need to lift the result by (i + 1).
  fn types_lookup(types: List‹KExpr›, i: G) -> KExpr {
    let ty = list_lookup(types, i);
    expr_lift(ty, i + 1, 0)
  }

  -- Mirror each KConstantInfo carries num_lvls as its first G field.
  fn const_num_lvls(ci: KConstantInfo) -> G {
    match ci {
      KConstantInfo.Axiom(n, _, _) => n,
      KConstantInfo.Defn(n, _, _, _, _) => n,
      KConstantInfo.Thm(n, _, _) => n,
      KConstantInfo.Opaque(n, _, _, _) => n,
      KConstantInfo.Quot(n, _, _) => n,
      KConstantInfo.Induct(n, _, _, _, _, _, _, _) => n,
      KConstantInfo.Ctor(n, _, _, _, _, _, _, _) => n,
      KConstantInfo.Rec(n, _, _, _, _, _, _, _, _, _, _) => n,
    }
  }

  -- Helpers: extract const declared type, Nat/Str literal types.
  fn const_type_of(ci: KConstantInfo) -> KExpr {
    match ci {
      KConstantInfo.Axiom(_, ty, _) => ty,
      KConstantInfo.Defn(_, ty, _, _, _) => ty,
      KConstantInfo.Thm(_, ty, _) => ty,
      KConstantInfo.Opaque(_, ty, _, _) => ty,
      KConstantInfo.Quot(_, ty, _) => ty,
      KConstantInfo.Induct(_, ty, _, _, _, _, _, _) => ty,
      KConstantInfo.Ctor(_, ty, _, _, _, _, _, _) => ty,
      KConstantInfo.Rec(_, ty, _, _, _, _, _, _, _, _, _) => ty,
    }
  }

  -- k_infer
  -- Mirror of `crates/kernel/src/infer.rs::infer`. Per-variant dispatch.
  -- Lvls placed at outermost; level-params instantiation handled where
  -- the constant's declared type is fetched.
  -- Context-trimmed memo wrapper (mirror Rust `infer_key`): key inference on
  -- the suffix of `types` reachable from `e`'s loose-bvar range, so a closed
  -- subterm (`lbr == 0`) shares its inferred type across every binder depth.
  fn k_infer(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> KExpr {
    let base = expr_lbr(e);
    match base {
      0 => k_infer_core(rc, e, store(ListNode.Nil)),
      _ => k_infer_rebase(rc, e, types, base),
    }
  }

  -- Rebase an OPEN subject to its minimum loose index before keying
  -- (the infer twin of k_def_eq_rebase; see that comment for the full
  -- argument). The suffix trim alone cannot canonicalize a subject
  -- that references only the OUTERMOST binders of a deep telescope:
  -- its lbr spans the whole context, the trim keeps every inner frame,
  -- and each inference site spells those (unreferenced) inner frames
  -- slightly differently — minting a fresh k_infer_core key per site.
  -- On `Simps.addProjections._unsafe_rec` (mathlib shard 211) this
  -- multiplicity produced 15.7M distinct k_check calls in 150s with no
  -- convergence. Frames below `g = min loose index` are loose in
  -- neither the subject nor the kept frames (which only ever reference
  -- deeper frames), so lowering by g and dropping those frames is a
  -- bijection on typing derivations (context strengthening by
  -- unreferenced frames). Unlike def-eq, which returns a bit,
  -- inference returns a TYPE valid in the context it ran in — so the
  -- result is lifted back by g.
  fn k_infer_rebase(rc: RoleCtx, e: KExpr, types: List‹KExpr›, base: G) -> KExpr {
    let g = lbr_min(expr_glb(e, 0), list_length(types));
    match g {
      0 => k_infer_core(rc, e, ctx_trim(types, base)),
      _ =>
        let t = k_infer_core(rc, expr_lower(e, g, 0),
                    ctx_trim(list_drop(types, g), base - g));
        expr_lift(t, g, 0),
    }
  }

  fn k_infer_core(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) => @types_lookup(types, i),

      KExprNode.Srt(l) =>
        store(KExprNode.Srt(level_reduce(store(KLevelNode.Succ(l))))),

      KExprNode.Const(addr, lvls) =>
        let ci = load(get_ci(addr));
        let expected = const_num_lvls(ci);
        let given = list_length(lvls);
        assert_eq!(given, expected,
          "Const applied to wrong number of universe levels");
        let ty = const_type_of(ci);
        expr_inst_levels(ty, lvls),

      KExprNode.App(_, _) =>
        match collect_spine(e) {
          (head, args) =>
            let head_ty = k_infer(rc, head, types);
            k_infer_app_spine_loop(rc, head_ty, args, store(ListNode.Nil), types),
        },

      KExprNode.Lam(ty, body) =>
        k_ensure_sort(rc, ty, types);
        let types2 = store(ListNode.Cons(ty, types));
        let body_ty = k_infer(rc, body, types2);
        store(KExprNode.Forall(ty, body_ty)),

      KExprNode.Forall(ty, body) =>
        let u1 = k_ensure_sort(rc, ty, types);
        let types2 = store(ListNode.Cons(ty, types));
        let u2 = k_ensure_sort(rc, body, types2);
        store(KExprNode.Srt(level_imax(u1, u2))),

      KExprNode.Let(ty, val, body) => k_infer_let_start(rc, ty, val, body, types),

      --  handlers:
      KExprNode.Lit(lit) => k_infer_lit(rc, lit),
      KExprNode.Proj(struct_addr, fidx, e1) =>
        k_infer_proj(rc, struct_addr, fidx, e1, types),
    }
  }

  -- Let-local inference environment. Values are closures in the environment
  -- before their declaration; checked types are concrete at the saved depth.
  -- Lambda locals keep their introduction depth, so extending the environment
  -- does not eagerly lift every earlier value. No new expression kind is
  -- introduced, and whnf/def-eq still consume ordinary concrete expressions.
  enum InferLetEnvNode {
    Id(List‹KExpr›, G),
    Local(KExpr, G, InferLetEnv),
    Let(KExpr, KExpr, InferLetEnv, G)
  }
  type InferLetEnv = &InferLetEnvNode

  fn k_infer_let_start(rc: RoleCtx, ty: KExpr, val: KExpr, body: KExpr,
                            types: List‹KExpr›) -> KExpr {
    k_ensure_sort(rc, ty, types);
    k_check(rc, val, ty, types);
    let depth = list_length(types);
    let env = store(InferLetEnvNode.Id(types, depth));
    k_infer_let_env(rc, body, store(InferLetEnvNode.Let(ty, val, env, depth)), types, depth)
  }

  fn infer_let_var_type(env: InferLetEnv, i: G,
                             types: List‹KExpr›, depth: G) -> KExpr {
    let (ty, created) = infer_let_lookup_type(env, i);
    expr_lift(ty, depth - created, 0)
  }

  fn infer_let_lookup_type(env: InferLetEnv, i: G) -> (KExpr, G) {
    match load(env) {
      InferLetEnvNode.Id(types, origin) => (types_lookup(types, i), origin),
      InferLetEnvNode.Local(ty, introduced, outer) => match i {
        0 => (ty, introduced - 1),
        _ => infer_let_lookup_type(outer, i - 1),
      },
      InferLetEnvNode.Let(ty, _, outer, created) => match i {
        0 => (ty, created),
        _ => infer_let_lookup_type(outer, i - 1),
      },
    }
  }

  fn infer_let_var_value(env: InferLetEnv, i: G, depth: G) -> KExpr {
    let (value, created) = infer_let_lookup_value(env, i);
    expr_lift(value, depth - created, 0)
  }

  fn infer_let_lookup_value(env: InferLetEnv, i: G) -> (KExpr, G) {
    match load(env) {
      InferLetEnvNode.Id(_, origin) => (store(KExprNode.BVar(i)), origin),
      InferLetEnvNode.Local(_, introduced, outer) => match i {
        0 => (store(KExprNode.BVar(0)), introduced),
        _ => infer_let_lookup_value(outer, i - 1),
      },
      InferLetEnvNode.Let(_, value, outer, created) => match i {
        0 => (infer_let_materialize(value, outer, created, 0), created),
        _ => infer_let_lookup_value(outer, i - 1),
      },
    }
  }

  fn infer_let_materialize(e: KExpr, env: InferLetEnv, depth: G, cutoff: G) -> KExpr {
    match memo_u32_less_than(cutoff, expr_lbr(e)) {
      0 => e,
      _ => match load(e) {
        KExprNode.BVar(i) => match memo_u32_less_than(i, cutoff) {
          1 => e,
          _ => expr_lift(@infer_let_var_value(env, i - cutoff, depth), cutoff, 0),
        },
        KExprNode.App(f, a) => store(KExprNode.App(
          infer_let_materialize(f, env, depth, cutoff), infer_let_materialize(a, env, depth, cutoff))),
        KExprNode.Lam(ty, body) => store(KExprNode.Lam(
          infer_let_materialize(ty, env, depth, cutoff), infer_let_materialize(body, env, depth, cutoff + 1))),
        KExprNode.Forall(ty, body) => store(KExprNode.Forall(
          infer_let_materialize(ty, env, depth, cutoff), infer_let_materialize(body, env, depth, cutoff + 1))),
        KExprNode.Let(ty, val, body) => store(KExprNode.Let(
          infer_let_materialize(ty, env, depth, cutoff), infer_let_materialize(val, env, depth, cutoff),
          infer_let_materialize(body, env, depth, cutoff + 1))),
        KExprNode.Proj(addr, i, val) => store(KExprNode.Proj(addr, i,
          infer_let_materialize(val, env, depth, cutoff))),
        _ => e,
      },
    }
  }

  fn k_infer_let_env(rc: RoleCtx, e: KExpr, env: InferLetEnv, types: List‹KExpr›, depth: G) -> KExpr {
    match expr_lbr(e) {
      0 => k_infer(rc, e, store(ListNode.Nil)),
      _ => match load(e) {
        -- Leave introductions delayed. Lowering a pure-let prefix can copy
        -- nested continuations without shrinking the real type context, so
        -- normalize applications only when a real local can be removed.
        KExprNode.App(_, _) => match infer_let_local_cutoff(env) {
          0 => k_infer_let_env_core(rc, e, env, types, depth),
          cutoff => match has_bvar_in_range(e, 0, cutoff) {
            1 => k_infer_let_env_core(rc, e, env, types, depth),
            0 => k_infer_let_env_rebase(rc, e, env, types, depth),
          },
        },
        _ => k_infer_let_env_core(rc, e, env, types, depth),
      },
    }
  }

  -- One plus the first Local's raw index, or zero if there is no Local.
  -- A real context slot can be removed exactly when the subject references
  -- none of this prefix. The short-circuiting occurrence test above avoids
  -- a full minimum-index walk when strengthening is impossible.
  fn infer_let_local_cutoff(env: InferLetEnv) -> G {
    match load(env) {
      InferLetEnvNode.Id(_, _) => 0,
      InferLetEnvNode.Local(_, _, _) => 1,
      InferLetEnvNode.Let(_, _, outer, _) => match infer_let_local_cutoff(outer) {
        0 => 0,
        n => n + 1,
      },
    }
  }

  fn k_infer_let_env_rebase(rc: RoleCtx, e: KExpr, env: InferLetEnv,
                          types: List‹KExpr›, depth: G) -> KExpr {
    let (outer, removed, locals) = infer_let_drop_unused(env, expr_glb(e, 0));
    let subject = expr_lower(e, removed, 0);
    let context = list_drop(types, locals);
    let ty = k_infer_let_env_core(rc, subject, outer, context, depth - locals);
    expr_lift(ty, locals, 0)
  }

  -- Forget leading bindings below the subject's minimum loose index.
  -- Their domains/values were already checked on entry to the environment.
  -- Every retained closure was created before those bindings, so cannot
  -- depend on them. Only Local nodes occupy real context slots: drop that
  -- many type entries, and lift the inferred type back by that count.
  -- Stop at Id and retain delayed application inference even there: rebasing
  -- changes only the context, not the application-substitution algorithm.
  fn infer_let_drop_unused(env: InferLetEnv, count: G) -> (InferLetEnv, G, G) {
    match count {
      0 => (env, 0, 0),
      _ => match load(env) {
        InferLetEnvNode.Let(_, _, outer, _) =>
          let (rest, removed, locals) = infer_let_drop_unused(outer, count - 1);
          (rest, removed + 1, locals),
        InferLetEnvNode.Local(_, _, outer) =>
          let (rest, removed, locals) = infer_let_drop_unused(outer, count - 1);
          (rest, removed + 1, locals + 1),
        _ => (env, 0, 0),
      },
    }
  }

  fn k_infer_let_env_core(rc: RoleCtx, e: KExpr, env: InferLetEnv,
                        types: List‹KExpr›, depth: G) -> KExpr {
    match load(e) {
        KExprNode.BVar(i) => @infer_let_var_type(env, i, types, depth),
        KExprNode.Lam(ty, body) =>
          let dom = infer_let_materialize(ty, env, depth, 0);
          k_ensure_sort(rc, dom, types);
          let inner_types = store(ListNode.Cons(dom, types));
          let inner_env = store(InferLetEnvNode.Local(dom, depth + 1, env));
          let body_ty = k_infer_let_env(rc, body, inner_env, inner_types, depth + 1);
          store(KExprNode.Forall(dom, body_ty)),
        KExprNode.Forall(ty, body) =>
          let dom = infer_let_materialize(ty, env, depth, 0);
          let u1 = k_ensure_sort(rc, dom, types);
          let inner_types = store(ListNode.Cons(dom, types));
          let inner_env = store(InferLetEnvNode.Local(dom, depth + 1, env));
          let bt = k_infer_let_env(rc, body, inner_env, inner_types, depth + 1);
          let KExprNode.Srt(u2) = load(whnf(rc, bt, inner_types));
          store(KExprNode.Srt(level_imax(u1, u2))),
        KExprNode.Let(ty, val, body) =>
          let dom = infer_let_materialize(ty, env, depth, 0);
          k_ensure_sort(rc, dom, types);
          let val_ty = k_infer_let_env(rc, val, env, types, depth);
          assert_eq!(k_is_def_eq(rc, val_ty, dom, types), 1, "delayed let value type mismatch");
          k_infer_let_env(rc, body, store(InferLetEnvNode.Let(dom, val, env, depth)), types, depth),
        KExprNode.App(f, a) =>
          let ft = k_infer_let_env(rc, f, env, types, depth);
          let KExprNode.Forall(dom, cod) = load(whnf(rc, ft, types));
          let arg_ty = k_infer_let_env(rc, a, env, types, depth);
          assert_eq!(k_is_def_eq(rc, arg_ty, dom, types), 1, "delayed application type mismatch");
          match has_bvar_in_range(cod, 0, 1) {
            0 => expr_lower(cod, 1, 1),
            _ => expr_inst1(cod, infer_let_materialize(a, env, depth, 0), 0),
          },
        _ => k_infer(rc, infer_let_materialize(e, env, depth, 0), types),
    }
  }

  -- Walk the head's Forall telescope arg-by-arg. `subs_rev` accumulates
  -- substituted args INNERMOST-FIRST (so substs[0] = latest arg = the one
  -- bound at BVar(0)). At each step we substitute prior args into the
  -- current Forall's `dom` (one expr_inst_many walk of the ORIGINAL dom,
  -- not a residual) for the check, then descend into `cod` with the
  -- extended subs. At spine end, one final expr_inst_many on the remaining
  -- `cod` yields the result type.
  -- When `load(t)` isn't a Forall, materialise via whnf on the concretised
  -- t (= prior subs applied to original t). Post-whnf dom/cod are in the
  -- OUTER context, so we restart the descent with subs_rev = [a].
  fn k_infer_app_spine_loop(rc: RoleCtx, t: KExpr, args: List‹KExpr›,
                                subs_rev: List‹KExpr›,
                                types: List‹KExpr›) -> KExpr {
    match load(args) {
      ListNode.Nil =>
        match list_length(subs_rev) {
          0 => t,
          _ => expr_inst_many(t, subs_rev, 0),
        },
      ListNode.Cons(a, rest) =>
        match load(t) {
          KExprNode.Forall(dom, cod) =>
            let dom_subst = match list_length(subs_rev) {
              0 => dom,
              _ => expr_inst_many(dom, subs_rev, 0),
            };
            k_check(rc, a, dom_subst, types);
            k_infer_app_spine_loop(rc, cod, rest,
              store(ListNode.Cons(a, subs_rev)), types),
          _ =>
            let t_concrete = match list_length(subs_rev) {
              0 => t,
              _ => expr_inst_many(t, subs_rev, 0),
            };
            let t_w = whnf(rc, t_concrete, types);
            match load(t_w) {
              KExprNode.Forall(dom, cod) =>
                k_check(rc, a, dom, types);
                k_infer_app_spine_loop(rc, cod, rest,
                  store(ListNode.Cons(a, store(ListNode.Nil))), types),
            },
        },
    }
  }

  -- A literal's type is the binding's `Nat` or `String`: typing a `Nat`
  -- literal needs the `Nat` role, a string literal the `String` role, which
  -- the claim then depends on (`role_used_implicitly`).
  fn k_infer_lit(rc: RoleCtx, lit: KLiteral) -> KExpr {
    match lit {
      KLiteral.Nat(_) => store(KExprNode.Const(role_addr(rc, role_nat()), store(ListNode.Nil))),
      KLiteral.Str(_) =>
        store(KExprNode.Const(role_used_implicitly(rc, role_string()), store(ListNode.Nil))),
    }
  }

  -- Peel `n_params` Foralls, substituting each with args[i].
  fn peel_params_subst(ty: KExpr, args: List‹KExpr›, n_params: G) -> KExpr {
    match n_params {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            match load(args) {
              ListNode.Cons(arg, rest) =>
                let body_substed = expr_inst1(body, arg, 0);
                peel_params_subst(body_substed, rest, n_params - 1),
            },
        },
    }
  }

  -- Walk ctor type's field foralls, substituting Proj(struct_addr, i, val)
  -- for each preceding field. At target field, return its dom.
  -- 1 iff the inductive's type, after peeling params+indices, lands in
  -- Sort 0. Mirror is_inductive_prop (Infer.lean:493).
  fn is_inductive_prop(rc: RoleCtx, ind_ty: KExpr, lvls: List‹KLevel›, n_skip: G,
                            types: List‹KExpr›) -> G {
    let ind_ty_inst = expr_inst_levels(ind_ty, lvls);
    let result = peel_n_alls_whnf(rc, ind_ty_inst, n_skip, types);
    -- No fallthrough arm: an inductive whose type does not peel to a
    -- Sort is malformed, and both references that implement this ERROR
    -- rather than answering — Rust `inductive_app_is_prop`
    -- (`infer.rs:485-517`, "projection: expected forall in inductive
    -- type", then `ensure_sort`) and `Ix/Tc` `inductiveAppIsProp`
    -- (`Infer.lean:296-324`), with the same message. lean4lean has no
    -- counterpart: `inferProj` infers the type of the APPLIED struct
    -- expression instead and never peels the declaration's telescope, so
    -- it offers no data point either way.
    --
    -- Answering 0 would be a false NEGATIVE — "not a Prop" — the unsafe
    -- direction, since it silently disables the Prop gates in
    -- `k_infer_proj` and would let a projection pull data out of a
    -- proof. `check_const`'s `check_inductive_shape` rejects such an
    -- inductive first, so this is defence in depth.
    match load(result) {
      KExprNode.Srt(l) => level_equal(l, store(KLevelNode.Zero)),
    }
  }

  -- Peel `n` Foralls, calling `whnf` on each step. Returns the whnf'd body.
  fn peel_n_alls_whnf(rc: RoleCtx, e: KExpr, n: G, types: List‹KExpr›) -> KExpr {
    match n {
      0 => whnf(rc, e, types),
      _ =>
        let ew = whnf(rc, e, types);
        match load(ew) {
          KExprNode.Forall(dom, body) =>
            let t2 = store(ListNode.Cons(dom, types));
            peel_n_alls_whnf(rc, body, n - 1, t2),
          _ => ew,
        },
    }
  }

  -- Prop-structure projection gates (mirror Infer.lean:507 / :457).
  -- Projecting out of a Prop-valued structure would extract data from a
  -- proof, breaking proof irrelevance. Two rules, both only for
  -- `is_prop` structures:
  --   * the TARGET field must itself be a Prop (Sort 0);
  --   * any data field skipped on the way must not be depended on by
  --     the remaining telescope (no loose bvars in the body).
  fn check_prop_field_if_prop(rc: RoleCtx, is_prop: G, dom: KExpr,
                                   types: List‹KExpr›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(rc, dom, types);
        assert_eq!(level_equal(lvl, store(KLevelNode.Zero)), 1,
          "projection on a Prop structure: field is not a Prop");
        (),
    }
  }

  -- Mirror crates/kernel/src/infer.rs dependent-data-field guard.
  -- For Prop structures: a preceding data field (sort != 0) whose body
  -- has any loose bvar (`body.lbr() > 0`) makes projection past it unsound.
  -- Matches Rust's `body.lbr() > 0` check exactly.
  fn check_no_dep_data_field_if_prop(rc: RoleCtx, is_prop: G, dom: KExpr, body: KExpr,
                                          types: List‹KExpr›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(rc, dom, types);
        match level_equal(lvl, store(KLevelNode.Zero)) {
          1 => (),
          _ =>
            -- data field: the rest of the telescope must not depend on it.
            assert_eq!(expr_lbr(body), 0,
              "projection on a Prop structure: later fields depend on a data field");
            (),
        },
    }
  }

  -- Mirror crates/kernel/src/infer.rs ctor-field walk loop.
  -- For each preceding field i < target_field, substitute body[Var(0)
  -- := Proj(struct_idx, i, val)] before recursing. At i == target_field,
  -- return the field's domain type.
  -- For Prop structures (`is_prop == 1`), enforce two soundness checks:
  -- (a) preceding data field whose body depends on BVar(0) is forbidden
  -- (no projection past dependent data fields, mirror Rust line 433-444);
  -- (b) projected (target) field must itself be in Prop (mirror Rust line 418-427).
  fn peel_field_loop(rc: RoleCtx, ty: KExpr, target: G, current: G,
                         struct_addr: Addr, val: KExpr, is_prop: G,
                         types: List‹KExpr›) -> KExpr {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match target - current {
          0 =>
            check_prop_field_if_prop(rc, is_prop, dom, types);
            dom,
          _ =>
            check_no_dep_data_field_if_prop(rc, is_prop, dom, body, types);
            let proj_expr = store(KExprNode.Proj(struct_addr, current, val));
            let body_substed = expr_inst1(body, proj_expr, 0);
            peel_field_loop(rc, body_substed, target, current + 1,
                                 struct_addr, val, is_prop, types),
        },
    }
  }

  -- Cold-extracted Proj arm: the widest arm of `k_infer_core` by far
  -- (~10 call sites) on a rare node kind.
  -- Mirror crates/kernel/src/infer.rs infer_proj.
  fn k_infer_proj(rc: RoleCtx, struct_addr: Addr, fidx: G, e1: KExpr,
                      types: List‹KExpr›) -> KExpr {
    let val_ty = k_infer(rc, e1, types);
    let wty = whnf(rc, val_ty, types);
    match collect_spine(wty) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(head_addr, lvls) =>
            assert_eq!(ptr_val(head_addr), ptr_val(struct_addr),
              "projection's structure type differs from the value's head");
            let ind_ci = load(get_ci(head_addr));
            match ind_ci {
              KConstantInfo.Induct(_, ind_ty, n_params, n_indices, num_ctors, _,
                                     block_addr, ind_idx) =>
                -- A projection is only meaningful on a structure: exactly one
                -- constructor, so field `fidx` names an unambiguous field and
                -- cidx=0 is the only choice. Without this a Proj on a
                -- multi-ctor inductive silently reads ctor 0's field types
                -- off a value built by a different ctor.
                assert_eq!(num_ctors, 1,
                  "projection on an inductive with more than one constructor");
                let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, 0));
                match ctor_ci {
                  KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _, _) =>
                    let ctor_ty_inst = expr_inst_levels(ctor_ty, lvls);
                    let after_params = peel_params_subst(ctor_ty_inst, args, n_params);
                    -- Prop-valued structures get the projection gates.
                    let is_prop = is_inductive_prop(rc, ind_ty, lvls,
                                    n_params + n_indices, types);
                    peel_field_loop(rc, after_params, fidx, 0,
                                         struct_addr, e1, is_prop, types),
                },
            },
        },
    }
  }

  -- No fallthrough arm: a value whose type does not whnf to a Sort is not
  -- a type, and the references error there too (Rust `ensure_sort`,
  -- `tc.rs:648-658`, returns `TcError::TypeExpected`; `Ix/Tc`
  -- `ensureSortWhnf` throws `.typeExpected`). Do not give it a default
  -- level — that would make an ill-typed `Lam` usable as a type.
  fn k_ensure_sort(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> KLevel {
    let t = k_infer(rc, e, types);
    let tw = whnf(rc, t, types);
    match load(tw) {
      KExprNode.Srt(l) => l,
    }
  }

  -- Check: infer the expr's type, def-eq against expected.
  fn k_check(rc: RoleCtx, e: KExpr, expected: KExpr, types: List‹KExpr›) {
    let inferred = k_infer(rc, e, types);
    let d = k_is_def_eq(rc, inferred, expected, types);
    assert_eq!(d, 1, "inferred type is not def-eq to the expected type");
  }

  -- ============================================================================
  -- Decidable dispatch.
  --
  -- The decision procedures are roles (`natDecEq`, `natDecLe`, `natDecLt`),
  -- each specified by one equation through `Decidable.decide`: `decide (d x y)`
  -- is a certified `Bool` operation of `x y`. On literal arguments the rule
  -- evaluates that operation to `v` and returns `isTrue P (of_decide_eq_true P
  -- (d a c) rfl)` or `isFalse P (of_decide_eq_false P (d a c) rfl)`. `decide`'s
  -- equations give that result the `decide` of `d a c`, and its
  -- extensionality makes them equal, so the rule computes an instance of the
  -- validated equations whatever shape the binding's `Decidable` has. `P` is
  -- built from the specification's type, not inferred.
  -- ============================================================================

  -- Entry point. Whnf calls this on Const-headed apps of family 5, the
  -- decision roles. Returns
  -- (1, reduced) on success or (0, _) to fall through to Defn unfold.
  fn try_dec_dispatch(rc: RoleCtx, head_addr: Addr, head_lvls: List‹KLevel›,
                          spine: List‹KExpr›, types: List‹KExpr›)
                          -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match role_is(rc, head_addr, role_nat_dec_lt()) {
          1 => dec_rewrite_lt_to_le(rc, spine, types),
          _ =>
        match role_is(rc, head_addr, role_nat_dec_le()) {
          1 => dec_nat(rc, 1, head_addr, head_lvls, spine, types),
          _ =>
        match role_is(rc, head_addr, role_nat_dec_eq()) {
          1 => dec_nat(rc, 0, head_addr, head_lvls, spine, types),
          _ =>
        match role_is(rc, head_addr, role_int_dec_lt()) {
          1 => dec_rewrite_int_lt_to_le(rc, spine, types),
          _ =>
        match role_is(rc, head_addr, role_int_dec_le()) {
          1 => dec_int(rc, 1, head_addr, head_lvls, spine, types),
          _ =>
        match role_is(rc, head_addr, role_int_dec_eq()) {
          1 => dec_int(rc, 0, head_addr, head_lvls, spine, types),
          _ => (0, store(KExprNode.BVar(0))),
        },
        },
        },
        },
        },
        },
    }
  }

  -- decLt n m → decLe (n+1) m, by `natDecLt`'s equation `decLt x y =
  -- decLe (succ x) y`: return (1, App(dec_le, succ_n_lit, m_e, ...post)).
  -- Whnf re-whnfs the rewritten form, which re-enters dispatch as decLe.
  fn dec_rewrite_lt_to_le(rc: RoleCtx, spine: List‹KExpr›,
                           types: List‹KExpr›) -> (G, KExpr) {
    let n_e = list_lookup(spine, 0);
    let m_e = list_lookup(spine, 1);
    let n_w = whnf(rc, n_e, types);
    match try_extract_nat(rc, n_w) {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, n_klimbs) =>
        let succ_lit = mk_nat_lit(klimbs_succ(n_klimbs));
        let dec_le_head = store(KExprNode.Const(
          role_addr(rc, role_nat_dec_le()), store(ListNode.Nil)));
        let app1 = store(KExprNode.App(dec_le_head, succ_lit));
        let app2 = store(KExprNode.App(app1, m_e));
        let post = list_drop(spine, 2);
        (1, apply_spine(app2, post)),
    }
  }

  -- `Nat.decLe n m` (is_le = 1) or `Nat.decEq n m` (is_le = 0) on literals:
  -- `decide` of it is `Nat.ble n m` or `Nat.beq n m` (the role's equation),
  -- evaluated natively. `P` is `Nat.le n m` or `@Eq Nat n m`.
  fn dec_nat(rc: RoleCtx, is_le: G, head_addr: Addr, head_lvls: List‹KLevel›,
              spine: List‹KExpr›, types: List‹KExpr›) -> (G, KExpr) {
    let n_e = list_lookup(spine, 0);
    let m_e = list_lookup(spine, 1);
    let n_w = whnf(rc, n_e, types);
    let m_w = whnf(rc, m_e, types);
    match try_extract_nat(rc, n_w) {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, n_kl) =>
        match try_extract_nat(rc, m_w) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, m_kl) =>
            let verdict = match is_le {
              1 => klimbs_le(n_kl, m_kl),
              _ => klimbs_eq(n_kl, m_kl),
            };
            let prop = match is_le {
              1 =>
                let le_c = store(KExprNode.Const(role_used_implicitly(rc, role_nat_le()),
                  store(ListNode.Nil)));
                store(KExprNode.App(store(KExprNode.App(le_c, n_e)), m_e)),
              _ => mk_eq1(rc, store(KExprNode.Const(role_addr(rc, role_nat()),
                  store(ListNode.Nil))), n_e, m_e),
            };
            let call = store(KExprNode.App(store(KExprNode.App(
              store(KExprNode.Const(head_addr, head_lvls)), n_e)), m_e));
            (1, apply_spine(dec_result(rc, verdict, prop, call), list_drop(spine, 2))),
        },
    }
  }

  -- `Int.decLt a b` → `Int.decLe (a + 1) b`, by `intDecLt`'s equation, with
  -- `a + 1` evaluated natively on a literal `a` (`intAdd`'s equations).
  -- Whnf re-whnfs the rewritten form, which re-enters dispatch as decLe.
  fn dec_rewrite_int_lt_to_le(rc: RoleCtx, spine: List‹KExpr›,
                               types: List‹KExpr›) -> (G, KExpr) {
    let a_e = list_lookup(spine, 0);
    let b_e = list_lookup(spine, 1);
    let a_w = whnf(rc, a_e, types);
    match try_extract_int_prim(rc, a_w) {
      (0, _, _) => (0, store(KExprNode.BVar(0))),
      (1, sa, na) =>
        let one = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
          store(ListNode.Nil)));
        let succ_a = int_add_prim(rc, sa, na, 0, one);
        let dec_le_head = store(KExprNode.Const(
          role_addr(rc, role_int_dec_le()), store(ListNode.Nil)));
        let app2 = store(KExprNode.App(store(KExprNode.App(dec_le_head, succ_a)), b_e));
        (1, apply_spine(app2, list_drop(spine, 2))),
    }
  }

  -- `Int.decLe a b` (is_le = 1) or `Int.decEq a b` (is_le = 0) on literals.
  -- The role's equations give `decide` of it at the four constructor pairs;
  -- the rule evaluates the same comparison in sign-magnitude form (`sign`
  -- 1 for `negSucc`, whose magnitude is at least 1). `P` is `Int.le a b` or
  -- `@Eq Int a b`.
  fn dec_int(rc: RoleCtx, is_le: G, head_addr: Addr, head_lvls: List‹KLevel›,
              spine: List‹KExpr›, types: List‹KExpr›) -> (G, KExpr) {
    let a_e = list_lookup(spine, 0);
    let b_e = list_lookup(spine, 1);
    let a_w = whnf(rc, a_e, types);
    let b_w = whnf(rc, b_e, types);
    match try_extract_int_prim(rc, a_w) {
      (0, _, _) => (0, store(KExprNode.BVar(0))),
      (1, sa, na) =>
        match try_extract_int_prim(rc, b_w) {
          (0, _, _) => (0, store(KExprNode.BVar(0))),
          (1, sb, nb) =>
            let verdict = match is_le {
              1 => int_le_verdict(sa, na, sb, nb),
              _ => (1 - (sa - sb) * (sa - sb)) * klimbs_eq(na, nb),
            };
            let prop = match is_le {
              1 =>
                let le_c = store(KExprNode.Const(role_used_implicitly(rc, role_int_le()),
                  store(ListNode.Nil)));
                store(KExprNode.App(store(KExprNode.App(le_c, a_e)), b_e)),
              _ => mk_eq1(rc, store(KExprNode.Const(role_used_implicitly(rc, role_int()),
                  store(ListNode.Nil))), a_e, b_e),
            };
            let call = store(KExprNode.App(store(KExprNode.App(
              store(KExprNode.Const(head_addr, head_lvls)), a_e)), b_e));
            (1, apply_spine(dec_result(rc, verdict, prop, call), list_drop(spine, 2))),
        },
    }
  }

  -- `a ≤ b` for sign-magnitude integers.
  fn int_le_verdict(sa: G, na: KLimbs, sb: G, nb: KLimbs) -> G {
    match sa {
      0 => match sb { 0 => klimbs_le(na, nb), _ => 0, },
      _ => match sb { 0 => 1, _ => klimbs_le(nb, na), },
    }
  }

  -- `@Eq.{1} ty a b`.
  fn mk_eq1(rc: RoleCtx, ty: KExpr, a: KExpr, b: KExpr) -> KExpr {
    let one_lvl = store(KLevelNode.Succ(store(KLevelNode.Zero)));
    let eq_c = store(KExprNode.Const(role_addr(rc, role_eq()),
      store(ListNode.Cons(one_lvl, store(ListNode.Nil)))));
    store(KExprNode.App(store(KExprNode.App(store(KExprNode.App(eq_c, ty)), a)), b))
  }

  -- The value of a decision `call : Decidable prop` whose `decide` is
  -- `verdict`: `Decidable.isTrue prop (of_decide_eq_true prop call (Eq.refl
  -- true))` or `Decidable.isFalse prop (of_decide_eq_false prop call (Eq.refl
  -- false))`. The constants it introduces are checked as the claim's
  -- dependencies.
  fn dec_result(rc: RoleCtx, verdict: G, prop: KExpr, call: KExpr) -> KExpr {
    let one_lvl = store(KLevelNode.Succ(store(KLevelNode.Zero)));
    let eq_refl_c = store(KExprNode.Const(role_addr(rc, role_eq_refl()),
      store(ListNode.Cons(one_lvl, store(ListNode.Nil)))));
    let bool_c = store(KExprNode.Const(role_addr(rc, role_bool()), store(ListNode.Nil)));
    let refl = store(KExprNode.App(store(KExprNode.App(eq_refl_c, bool_c)), mk_bool(rc, verdict)));
    let of_decide = match verdict {
      1 => role_used_implicitly(rc, role_of_decide_eq_true()),
      _ => role_used_implicitly(rc, role_of_decide_eq_false()),
    };
    let ctor = match verdict {
      1 => role_used_implicitly(rc, role_decidable_is_true()),
      _ => role_used_implicitly(rc, role_decidable_is_false()),
    };
    let proof = store(KExprNode.App(store(KExprNode.App(store(KExprNode.App(
      store(KExprNode.Const(of_decide, store(ListNode.Nil))), prop)), call)), refl));
    store(KExprNode.App(store(KExprNode.App(
      store(KExprNode.Const(ctor, store(ListNode.Nil))), prop)), proof))
  }

  -- String.decEq on two Lit(Str)-whnf'd args, when the bytestreams are equal:
  -- the generic decision result for `decide (String.decEq s s) = true`, the
  -- role's equation. Unequal bails. Entry point invoked from Whnf's
  -- string primitive dispatch when head_addr matches string_dec_eq.
  --
  -- head_addr, spine assumed pre-whnf'd (caller runs whnf_spine).
  fn try_str_dec_eq(rc: RoleCtx, head_addr: Addr, spine: List‹KExpr›,
                        types: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let a0 = list_lookup(spine, 0);
        let a1 = list_lookup(spine, 1);
        match load(a0) {
          KExprNode.Lit(la) =>
            match la {
              KLiteral.Str(sa) =>
                match load(a1) {
                  KExprNode.Lit(lb) =>
                    match lb {
                      KLiteral.Str(sb) =>
                        match bytestream_eq(sa, sb) {
                          0 => (0, store(KExprNode.BVar(0))),
                          _ =>
                            let str_c = store(KExprNode.Const(role_addr(rc, role_string()),
                              store(ListNode.Nil)));
                            let call = store(KExprNode.App(store(KExprNode.App(
                              store(KExprNode.Const(head_addr, store(ListNode.Nil))), a0)), a1));
                            (1, apply_spine(dec_result(rc, 1, mk_eq1(rc, str_c, a0, a1), call),
                              list_drop(spine, 2))),
                        },
                      _ => (0, store(KExprNode.BVar(0))),
                    },
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

⟧

end IxVM

end

