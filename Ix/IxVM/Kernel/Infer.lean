module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Whnf
public import Ix.IxVM.Kernel.DefEq

public section

namespace IxVM

/-! ## Type inference over `KExpr`

Mirrors `src/ix/kernel/infer.rs::infer`.

Binder bodies are opened on entry: when we recurse into `Lam(ty, body)`,
`Forall(ty, body)`, or `Let(ty, val, body)`, we replace `BVar(0)` in `body`
with `FVar(fresh, ty)` and decrement remaining loose `BVar`s via
`expr_inst1`. `fresh` is the current binder depth (= `list_length types`),
so distinct opened binders get distinct indices. Recursion then sees a
"locally nameless" body where the previously-bound variable shows up as
a free variable carrying its own declared type.

`BVar(i)` lookups still use `types` and the lift-by-`i+1` convention,
so non-opened binders deeper in the surrounding context continue to
work. `FVar(_, ty)` just returns `ty` directly — no lift needed since
the type was assembled at the opening site under the outer context.

When wrapping an inferred body's type back into a `Forall`, we close it
by replacing `FVar(fresh, _)` with `BVar(0)` and shifting loose BVars up
(`expr_close`).
-/

def infer := ⟦
  -- ============================================================================
  -- k_infer
  --
  -- Mirror of `src/ix/kernel/infer.rs::infer`. Per-variant dispatch.
  --
  -- Lvls placed at outermost; level-params instantiation handled where
  -- the constant's declared type is fetched.
  -- ============================================================================
  fn k_infer(e: KExpr, depth: G,
             top: List‹&KConstantInfo›, addrs: List‹[G; 32]›) -> KExpr {
    match load(e) {
      -- The `BVar` case should be impossible: callers hand in
      -- FVar-opened expressions where every loose bound variable has
      -- been substituted by an `FVar`. Aiur panics ("no match case
      -- for value 0") if a leaf BVar slips through.
      KExprNode.FVar(_, ty) => ty,
      -- Normalize the constructed `Succ(l)` so callers see canonical
      -- forms (e.g. `Succ(IMax 0 1)` → `Succ(Succ Zero) = 2`). Without
      -- this, `level_leq` for cases like `levelComp2` (`Sort(IMax 0 1)`)
      -- has to compare `Succ(IMax 0 1)` against `Succ(Succ Zero)`
      -- structurally and the case-split paths can diverge.
      KExprNode.Srt(l) =>
        store(KExprNode.Srt(store(level_reduce(KLevel.Succ(l))))),

      -- Mirror: src/ix/kernel/check.rs:110-120 universe-arity validation.
      -- Validates `lvls.len() == num_lvls(ci)`.
      KExprNode.Const(idx, lvls) =>
        let ci = load(list_lookup(top, idx));
        let expected = const_num_lvls(ci);
        let given = list_length(lvls);
        assert_eq!(given, expected);
        let ty = const_type_of(ci);
        expr_inst_levels(ty, lvls),

      KExprNode.App(f, a) =>
        let f_ty = k_infer(f, depth, top, addrs);
        -- Mirror: src/ix/kernel/infer.rs:454-478 peel_proj_forall syntactic fast-path.
        match load(f_ty) {
          KExprNode.Forall(dom, cod) =>
            let _ = k_check(a, dom, depth, top, addrs);
            expr_subst1(cod, a, 0),
          _ =>
            let f_ty_whnf = whnf(f_ty, depth, top, addrs);
            let triple = ensure_forall_post_whnf(f_ty_whnf);
            match triple {
              (ok, dom, cod) =>
                assert_eq!(ok, 1);
                let _ = k_check(a, dom, depth, top, addrs);
                expr_subst1(cod, a, 0),
            },
        },

      -- Open body via `expr_subst1(body, fv, 0)`: substitute `BVar(0)`
      -- with the fresh FVar and decrement remaining loose BVars so they
      -- index the outer `types` context directly (no shadow extension).
      -- `fid = depth` distinguishes binders across nesting
      -- since each opening grows `types` by one entry used as a depth
      -- counter (BVar lookups under the invariant should never reach
      -- the shadow slot).
      KExprNode.Lam(ty, body) =>
        let _ = k_ensure_sort(ty, depth, top, addrs);
        let fid = depth;
        let fv = store(KExprNode.FVar(fid, ty));
        let body_open = expr_subst1(body, fv, 0);
        let depth2 = depth + 1;
        let body_ty_open = k_infer(body_open, depth2, top, addrs);
        let body_ty = expr_close(body_ty_open, fid, 0);
        store(KExprNode.Forall(ty, body_ty)),

      KExprNode.Forall(ty, body) =>
        let u1 = k_ensure_sort(ty, depth, top, addrs);
        let fid = depth;
        let fv = store(KExprNode.FVar(fid, ty));
        let body_open = expr_subst1(body, fv, 0);
        let depth2 = depth + 1;
        let u2 = k_ensure_sort(body_open, depth2, top, addrs);
        store(KExprNode.Srt(store(level_imax(load(u1), load(u2))))),

      -- Let is a definitional binder, not a quantifier: the result type
      -- of `let x : ty := val in body` is `body`'s type with `x` replaced
      -- by `val`, not by a fresh free variable. Substituting `val` keeps
      -- the result closed in the surrounding context with no outer
      -- binder to re-introduce.
      KExprNode.Let(ty, val, body) =>
        let _ = k_ensure_sort(ty, depth, top, addrs);
        let _ = k_check(val, ty, depth, top, addrs);
        let body_substed = expr_subst1(body, val, 0);
        k_infer(body_substed, depth, top, addrs),

      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) => nat_const_type(addrs),
          KLiteral.Str(_) => str_const_type(addrs),
        },

      -- Mirror: src/ix/kernel/infer.rs:331-450 infer_proj.
      KExprNode.Proj(tidx, fidx, e1) =>
        let val_ty = k_infer(e1, depth, top, addrs);
        let wty = whnf(val_ty, depth, top, addrs);
        let pair = collect_spine(wty);
        match pair {
          (head, args) =>
            match load(head) {
              KExprNode.Const(idx, lvls) =>
                assert_eq!(idx, tidx);
                let ind_ci = load(list_lookup(top, idx));
                match ind_ci {
                  KConstantInfo.Induct(_, ind_ty, n_params, n_indices, ctor_indices, _, _, _, _, _) =>
                    -- Single-ctor structure required.
                    assert_eq!(list_length(ctor_indices), 1);
                    let is_prop = is_inductive_prop(ind_ty, lvls, n_params + n_indices,
                                                     depth, top, addrs);
                    let ctor_idx = list_lookup(ctor_indices, 0);
                    let ctor_ci = load(list_lookup(top, ctor_idx));
                    match ctor_ci {
                      KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _) =>
                        let ctor_ty_inst = expr_inst_levels(ctor_ty, lvls);
                        let after_params = peel_params_subst(ctor_ty_inst, args, n_params);
                        peel_field_loop(after_params, fidx, 0, tidx, e1, is_prop,
                                        depth, top, addrs),
                    },
                },
            },
        },
    }
  }

  fn k_ensure_sort(e: KExpr, depth: G,
                   top: List‹&KConstantInfo›, addrs: List‹[G; 32]›) -> &KLevel {
    let ty = k_infer(e, depth, top, addrs);
    -- Mirror: src/ix/kernel/infer.rs:454-478 syntactic Sort fast-path.
    match load(ty) {
      KExprNode.Srt(l) => l,
      _ =>
        let ty_whnf = whnf(ty, depth, top, addrs);
        let pair = ensure_sort_post_whnf(ty_whnf);
        match pair {
          (ok, l) =>
            assert_eq!(ok, 1);
            l,
        },
    }
  }

  -- Mirror: src/ix/kernel/infer.rs App-arg / Let-val pattern. Infer e's
  -- type and compare against expected via k_is_def_eq. Mismatch panics.
  fn k_check(e: KExpr, expected: KExpr, depth: G,
             top: List‹&KConstantInfo›, addrs: List‹[G; 32]›) {
    let inferred = k_infer(e, depth, top, addrs);
    let eq = k_is_def_eq(inferred, expected, depth, top, addrs);
    assert_eq!(eq, 1);
    ()
  }

  -- ============================================================================
  -- Helpers: extract const declared type, Nat/Str literal types.
  -- ============================================================================
  fn const_type_of(ci: KConstantInfo) -> KExpr {
    match ci {
      KConstantInfo.Axiom(_, ty, _) => ty,
      KConstantInfo.Defn(_, ty, _, _, _) => ty,
      KConstantInfo.Thm(_, ty, _) => ty,
      KConstantInfo.Opaque(_, ty, _, _) => ty,
      KConstantInfo.Quot(_, ty, _) => ty,
      KConstantInfo.Induct(_, ty, _, _, _, _, _, _, _, _) => ty,
      KConstantInfo.Ctor(_, ty, _, _, _, _, _) => ty,
      KConstantInfo.Rec(_, ty, _, _, _, _, _, _, _, _) => ty,
    }
  }

  -- Mirror: each KConstantInfo carries num_lvls as its first G field.
  fn const_num_lvls(ci: KConstantInfo) -> G {
    match ci {
      KConstantInfo.Axiom(n, _, _) => n,
      KConstantInfo.Defn(n, _, _, _, _) => n,
      KConstantInfo.Thm(n, _, _) => n,
      KConstantInfo.Opaque(n, _, _, _) => n,
      KConstantInfo.Quot(n, _, _) => n,
      KConstantInfo.Induct(n, _, _, _, _, _, _, _, _, _) => n,
      KConstantInfo.Ctor(n, _, _, _, _, _, _) => n,
      KConstantInfo.Rec(n, _, _, _, _, _, _, _, _, _) => n,
    }
  }

  -- Mirror: peel n_params Foralls off ctor_ty, substituting each
  -- bound var with the corresponding `args[i]`. Used by infer_proj.
  fn peel_params_subst(ty: KExpr, args: List‹KExpr›, n_params: G) -> KExpr {
    match n_params {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            match load(args) {
              ListNode.Cons(arg, rest) =>
                let body_substed = expr_subst1(body, arg, 0);
                peel_params_subst(body_substed, rest, n_params - 1),
            },
        },
    }
  }

  -- Mirror: src/ix/kernel/infer.rs:414-449 ctor-field walk loop.
  -- For each preceding field i < target_field, substitute body[Var(0)
  -- := Proj(struct_idx, i, val)] before recursing. At i == target_field,
  -- return the field's domain type.
  --
  -- For Prop structures (`is_prop == 1`), enforce two soundness checks:
  --   (a) preceding data field whose body depends on BVar(0) is forbidden
  --       (no projection past dependent data fields, mirror Rust line 433-444);
  --   (b) projected (target) field must itself be in Prop (mirror Rust line 418-427).
  fn peel_field_loop(ty: KExpr, target_field: G, current: G,
                     struct_idx: G, val: KExpr, is_prop: G,
                     depth: G, top: List‹&KConstantInfo›,
                     addrs: List‹[G; 32]›) -> KExpr {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match target_field - current {
          0 =>
            let _ = check_prop_field_if_prop(is_prop, dom, depth, top, addrs);
            dom,
          _ =>
            let _ = check_no_dep_data_field_if_prop(is_prop, dom, body, depth, top, addrs);
            let proj_expr = store(KExprNode.Proj(struct_idx, current, val));
            let body_substed = expr_subst1(body, proj_expr, 0);
            peel_field_loop(body_substed, target_field, current + 1,
              struct_idx, val, is_prop, depth, top, addrs),
        },
    }
  }

  -- Mirror: src/ix/kernel/infer.rs:431-444 dependent-data-field guard.
  -- For Prop structures: a preceding data field (sort != 0) whose body
  -- has any loose bvar (`body.lbr() > 0`) makes projection past it unsound.
  -- Matches Rust's `body.lbr() > 0` check exactly.
  fn check_no_dep_data_field_if_prop(is_prop: G, dom: KExpr, body: KExpr,
                                       depth: G,
                                       top: List‹&KConstantInfo›,
                                       addrs: List‹[G; 32]›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(dom, depth, top, addrs);
        match level_equal(load(lvl), KLevel.Zero) {
          1 => (),
          _ =>
            -- data field; body must have no loose bvars.
            assert_eq!(expr_lbr(body), 0);
            (),
        },
    }
  }

  -- Peel `n` Foralls, calling `whnf` on each step. Returns the whnf'd body.
  fn peel_n_alls_whnf(e: KExpr, n: G, depth: G,
                      top: List‹&KConstantInfo›, addrs: List‹[G; 32]›) -> KExpr {
    match n {
      0 => whnf(e, depth, top, addrs),
      _ =>
        let ew = whnf(e, depth, top, addrs);
        match load(ew) {
          KExprNode.Forall(_, body) =>
            peel_n_alls_whnf(body, n - 1, depth, top, addrs),
          _ => ew,
        },
    }
  }

  -- Mirror: src/ix/kernel/infer.rs:488-520 inductive_app_is_prop.
  -- Returns 1 iff the inductive lives in Prop (peeled past params + indices,
  -- result sort = Zero).
  fn is_inductive_prop(ind_ty: KExpr, lvls: List‹&KLevel›, n_skip: G,
                       depth: G, top: List‹&KConstantInfo›,
                       addrs: List‹[G; 32]›) -> G {
    let ind_ty_inst = expr_inst_levels(ind_ty, lvls);
    let result = peel_n_alls_whnf(ind_ty_inst, n_skip, depth, top, addrs);
    match load(result) {
      KExprNode.Srt(l) => level_equal(load(l), KLevel.Zero),
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/infer.rs:418-427 Prop-projection guard. When
  -- projecting a field from a Prop-typed structure, the field MUST itself
  -- live in Prop. Otherwise projection violates proof irrelevance.
  fn check_prop_field_if_prop(is_prop: G, dom: KExpr, depth: G,
                               top: List‹&KConstantInfo›, addrs: List‹[G; 32]›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(dom, depth, top, addrs);
        assert_eq!(level_equal(load(lvl), KLevel.Zero), 1);
        (),
    }
  }

  -- Address-keyed literal-type lookup.
  -- Walks `addrs` to find the kernel position of Nat / String. Builds
  -- `Const(idx, [])` for the type of `Lit(Nat _)` / `Lit(Str _)`.
  fn nat_const_type(addrs: List‹[G; 32]›) -> KExpr {
    let idx = find_addr_idx(nat_addr(), addrs, 0);
    store(KExprNode.Const(idx, store(ListNode.Nil)))
  }

  fn str_const_type(addrs: List‹[G; 32]›) -> KExpr {
    let idx = find_addr_idx(str_addr(), addrs, 0);
    store(KExprNode.Const(idx, store(ListNode.Nil)))
  }

  -- Find the position of `target` in `addrs`. Panics (no Nil arm) if
  -- not present — caller (literal typing) requires it.
  fn find_addr_idx(target: [G; 32], addrs: List‹[G; 32]›, i: G) -> G {
    match load(addrs) {
      ListNode.Cons(a, rest) =>
        match address_eq(target, a) {
          1 => i,
          0 => find_addr_idx(target, rest, i + 1),
        },
    }
  }
⟧

end IxVM

end
