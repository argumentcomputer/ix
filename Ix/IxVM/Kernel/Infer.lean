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

Local context is a `List‹KExpr›` of binder types in innermost-first order.
A `BVar(i)` looks up `types[i]` and lifts it by `i + 1` (since the binder
was bound `i + 1` levels up).

For `Lam(ty, body)`, the inferred type is `Forall(ty, body_type)` where
`body_type` is computed under `types ++ [ty]` (which means `Cons(ty, types)`).
No fvars — we work directly with de Bruijn indices.
-/

def infer := ⟦
  -- ============================================================================
  -- Context lookup with lift
  --
  -- types[i] is the type of the i-th binder from the innermost. When we
  -- look up BVar(i), we get types[i] but it was assembled at depth d-i-1
  -- (counting from outermost). The current context is at depth d, so we
  -- need to lift the result by (i + 1).
  -- ============================================================================
  fn types_lookup(types: List‹KExpr›, i: G) -> KExpr {
    match load(types) {
      ListNode.Nil => store(KExprNode.BVar(0)),
      ListNode.Cons(ty, rest) =>
        match i {
          0 => expr_lift(ty, 1, 0),
          _ =>
            let inner = types_lookup(rest, i - 1);
            expr_lift(inner, 1, 0),
        },
    }
  }

  -- ============================================================================
  -- k_infer
  --
  -- Mirror of `src/ix/kernel/infer.rs::infer`. Per-variant dispatch.
  --
  -- Lvls placed at outermost; level-params instantiation handled where
  -- the constant's declared type is fetched.
  -- ============================================================================
  fn k_infer(e: KExpr, types: List‹KExpr›,
             top: List‹&KConstantInfo›, addrs: List‹Addr›) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) => types_lookup(types, i),

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
        let f_ty = k_infer(f, types, top, addrs);
        -- Mirror: src/ix/kernel/infer.rs:454-478 peel_proj_forall syntactic fast-path.
        match load(f_ty) {
          KExprNode.Forall(dom, cod) =>
            let _ = k_check(a, dom, types, top, addrs);
            expr_inst1(cod, a, 0),
          _ =>
            let f_ty_whnf = whnf(f_ty, types, top, addrs);
            let triple = ensure_forall_post_whnf(f_ty_whnf);
            match triple {
              (ok, dom, cod) =>
                assert_eq!(ok, 1);
                let _ = k_check(a, dom, types, top, addrs);
                expr_inst1(cod, a, 0),
            },
        },

      KExprNode.Lam(ty, body) =>
        let _ = k_ensure_sort(ty, types, top, addrs);
        let types2 = store(ListNode.Cons(ty, types));
        let body_ty = k_infer(body, types2, top, addrs);
        store(KExprNode.Forall(ty, body_ty)),

      KExprNode.Forall(ty, body) =>
        let u1 = k_ensure_sort(ty, types, top, addrs);
        let types2 = store(ListNode.Cons(ty, types));
        let u2 = k_ensure_sort(body, types2, top, addrs);
        store(KExprNode.Srt(store(level_imax(load(u1), load(u2))))),

      KExprNode.Let(ty, val, body) =>
        let _ = k_ensure_sort(ty, types, top, addrs);
        let _ = k_check(val, ty, types, top, addrs);
        let body_substed = expr_inst1(body, val, 0);
        k_infer(body_substed, types, top, addrs),

      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) => nat_const_type(addrs),
          KLiteral.Str(_) => str_const_type(addrs),
        },

      -- Mirror: src/ix/kernel/infer.rs:331-450 infer_proj.
      KExprNode.Proj(tidx, fidx, e1) =>
        let val_ty = k_infer(e1, types, top, addrs);
        let wty = whnf(val_ty, types, top, addrs);
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
                                                     types, top, addrs);
                    let ctor_idx = list_lookup(ctor_indices, 0);
                    let ctor_ci = load(list_lookup(top, ctor_idx));
                    match ctor_ci {
                      KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _) =>
                        let ctor_ty_inst = expr_inst_levels(ctor_ty, lvls);
                        let after_params = peel_params_subst(ctor_ty_inst, args, n_params);
                        peel_field_loop(after_params, fidx, 0, tidx, e1, is_prop,
                                        types, top, addrs),
                    },
                },
            },
        },
    }
  }

  fn k_ensure_sort(e: KExpr, types: List‹KExpr›,
                   top: List‹&KConstantInfo›, addrs: List‹Addr›) -> &KLevel {
    let ty = k_infer(e, types, top, addrs);
    -- Mirror: src/ix/kernel/infer.rs:454-478 syntactic Sort fast-path.
    match load(ty) {
      KExprNode.Srt(l) => l,
      _ =>
        let ty_whnf = whnf(ty, types, top, addrs);
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
  fn k_check(e: KExpr, expected: KExpr, types: List‹KExpr›,
             top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    let inferred = k_infer(e, types, top, addrs);
    let eq = k_is_def_eq(inferred, expected, types, top, addrs);
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
                let body_substed = expr_inst1(body, arg, 0);
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
                     types: List‹KExpr›, top: List‹&KConstantInfo›,
                     addrs: List‹Addr›) -> KExpr {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match target_field - current {
          0 =>
            let _ = check_prop_field_if_prop(is_prop, dom, types, top, addrs);
            dom,
          _ =>
            let _ = check_no_dep_data_field_if_prop(is_prop, dom, body, types, top, addrs);
            let proj_expr = store(KExprNode.Proj(struct_idx, current, val));
            let body_substed = expr_inst1(body, proj_expr, 0);
            peel_field_loop(body_substed, target_field, current + 1,
              struct_idx, val, is_prop, types, top, addrs),
        },
    }
  }

  -- Mirror: src/ix/kernel/infer.rs:431-444 dependent-data-field guard.
  -- For Prop structures: a preceding data field (sort != 0) whose body
  -- has any loose bvar (`body.lbr() > 0`) makes projection past it unsound.
  -- Matches Rust's `body.lbr() > 0` check exactly.
  fn check_no_dep_data_field_if_prop(is_prop: G, dom: KExpr, body: KExpr,
                                       types: List‹KExpr›,
                                       top: List‹&KConstantInfo›,
                                       addrs: List‹Addr›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(dom, types, top, addrs);
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
  fn peel_n_alls_whnf(e: KExpr, n: G, types: List‹KExpr›,
                      top: List‹&KConstantInfo›, addrs: List‹Addr›) -> KExpr {
    match n {
      0 => whnf(e, types, top, addrs),
      _ =>
        let ew = whnf(e, types, top, addrs);
        match load(ew) {
          KExprNode.Forall(_, body) =>
            peel_n_alls_whnf(body, n - 1, types, top, addrs),
          _ => ew,
        },
    }
  }

  -- Mirror: src/ix/kernel/infer.rs:488-520 inductive_app_is_prop.
  -- Returns 1 iff the inductive lives in Prop (peeled past params + indices,
  -- result sort = Zero).
  fn is_inductive_prop(ind_ty: KExpr, lvls: List‹&KLevel›, n_skip: G,
                       types: List‹KExpr›, top: List‹&KConstantInfo›,
                       addrs: List‹Addr›) -> G {
    let ind_ty_inst = expr_inst_levels(ind_ty, lvls);
    let result = peel_n_alls_whnf(ind_ty_inst, n_skip, types, top, addrs);
    match load(result) {
      KExprNode.Srt(l) => level_equal(load(l), KLevel.Zero),
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/infer.rs:418-427 Prop-projection guard. When
  -- projecting a field from a Prop-typed structure, the field MUST itself
  -- live in Prop. Otherwise projection violates proof irrelevance.
  fn check_prop_field_if_prop(is_prop: G, dom: KExpr, types: List‹KExpr›,
                               top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(dom, types, top, addrs);
        assert_eq!(level_equal(load(lvl), KLevel.Zero), 1);
        (),
    }
  }

  -- Address-keyed literal-type lookup.
  -- Walks `addrs` to find the kernel position of Nat / String. Builds
  -- `Const(idx, [])` for the type of `Lit(Nat _)` / `Lit(Str _)`.
  fn nat_const_type(addrs: List‹Addr›) -> KExpr {
    let idx = find_addr_idx(nat_addr(), addrs, 0);
    store(KExprNode.Const(idx, store(ListNode.Nil)))
  }

  fn str_const_type(addrs: List‹Addr›) -> KExpr {
    let idx = find_addr_idx(str_addr(), addrs, 0);
    store(KExprNode.Const(idx, store(ListNode.Nil)))
  }

  -- Find the position of `target` in `addrs`. Panics (no Nil arm) if
  -- not present — caller (literal typing) requires it.
  fn find_addr_idx(target: Addr, addrs: List‹Addr›, i: G) -> G {
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
