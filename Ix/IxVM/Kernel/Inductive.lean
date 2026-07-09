module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Inductive block validation

Mirror: `src/ix/kernel/inductive.rs` (parameter agreement, return-type
validation, universe constraints, strict positivity, recursor synthesis).

Structure-only validation, no name diagnostics.
-/

def inductive_check := ⟦
  -- Mirror: src/ix/kernel/inductive.rs:1968-2080 check_ctor_return_type.
  -- Validates that a ctor's declared type, after peeling
  -- `n_params + n_fields` Foralls, is a syntactic `Indc(params, indices)`
  -- application:
  --   * head is `Const(ind_idx, lvls)`
  --   * `lvls.len() == ind_num_lvls`
  --   * each `lvls[i]` is `Param(i)`
  --   * spine args count is `n_params + n_indices`
  --   * first `n_params` args are the param BVars (de Bruijn equivalents
  --     of Rust's param fvars at line 1986-1994).
  --
  -- Failure path: `assert_eq!(0, 1)` panics the Aiur execution per the
  -- kernel's accept/reject convention.
  fn check_ctor_return_type(ctor_ty: KExpr,
                            n_params: G, n_indices: G, n_fields: G,
                            ind_idx: G, ind_num_lvls: G) {
    let body = peel_n_foralls(ctor_ty, n_params + n_fields);
    let pair = collect_spine(body);
    match pair {
      (head, args) =>
        match load(head) {
          KExprNode.Const(idx, lvls) =>
            assert_eq!(idx, ind_idx);
            assert_lvls_are_params(lvls, ind_num_lvls, 0);
            let args_len = list_length(args);
            assert_eq!(args_len, n_params + n_indices);
            assert_first_args_are_param_bvars(args, n_params, n_fields, 0);
            (),
        },
    }
  }

  -- Peel `n` Foralls off the head, return the body. Panics if fewer
  -- Foralls than requested.
  fn peel_n_foralls(e: KExpr, n: G) -> KExpr {
    match n {
      0 => e,
      _ =>
        match load(e) {
          KExprNode.Forall(_, body) => peel_n_foralls(body, n - 1),
        },
    }
  }

  -- Each `lvls[i]` must be `Param(expected_start + i)` for i in 0..count.
  fn assert_lvls_are_params(lvls: List‹KLevel›, count: G, idx: G) {
    match count {
      0 =>
        -- Mirror: src/ix/kernel/inductive.rs:2018: us.len() == ind_lvls.
        -- At base case all expected lvls consumed; remaining list must be empty.
        assert_eq!(list_length(lvls), 0);
        (),
      _ =>
        match load(lvls) {
          ListNode.Cons(l, rest) =>
            match load(l) {
              KLevelNode.Param(i) =>
                assert_eq!(i, idx);
                assert_lvls_are_params(rest, count - 1, idx + 1);
                (),
            },
        },
    }
  }

  -- The first `n_params` args of the spine must be exactly
  -- `BVar(n_fields + n_params - 1 - i)` for i in 0..n_params, i.e. the
  -- de Bruijn references to the param binders peeled off the ctor's
  -- type. The remaining args are the indices — those are unrestricted
  -- here (per Rust 2046+).
  fn assert_first_args_are_param_bvars(args: List‹KExpr›,
                                        n_params: G, n_fields: G, i: G) {
    -- `n_params` is the TOTAL param count (constant across recursion);
    -- iterate i = 0..n_params. Expected j = (n_fields + n_params) - 1 - i
    -- where i is the param index from outermost, so arg[0] points at the
    -- outermost binder (highest BVar) and arg[n_params-1] at the innermost.
    match n_params - i {
      0 => (),
      _ =>
        match load(args) {
          ListNode.Cons(arg, rest) =>
            match load(arg) {
              KExprNode.BVar(j) =>
                assert_eq!(j, ((n_fields + n_params) - 1) - i);
                assert_first_args_are_param_bvars(rest, n_params, n_fields, i + 1);
                (),
            },
        },
    }
  }

  -- Extract the inductive's result-sort level: peel `n` (params + indices)
  -- Foralls; the body must be `Srt(level)`. Returns the level value.
  -- Mirror: src/ix/kernel/inductive.rs::get_result_sort_level (line 2089+).
  fn get_result_sort_level(ind_ty: KExpr, n: G) -> KLevel {
    match n {
      0 =>
        match load(ind_ty) {
          KExprNode.Srt(l) => l,
        },
      _ =>
        match load(ind_ty) {
          KExprNode.Forall(_, body) => get_result_sort_level(body, n - 1),
        },
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:1917-1965 check_field_universes.
  -- Each ctor field's domain universe must be ≤ the inductive's
  -- result universe. Skipped for Prop (Sort 0) per Rust line 1924.
  --
  -- Walks the ctor type past `n_params` Foralls (param binders),
  -- threading the binder types into `types`. Then on each remaining
  -- Forall (a field), ensures `dom`'s sort level is ≤ ind_level via
  -- `k_ensure_sort` + `level_leq`.
  fn check_field_universes(ctor_ty: KExpr, n_params: G, ind_level: KLevel,
                           types: List‹KExpr›,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    -- Skip if inductive is Prop.
    match load(ind_level) {
      KLevelNode.Zero => (),
      _ => check_field_universes_skip_params(ctor_ty, n_params, ind_level, types, top, addrs),
    }
  }

  fn check_field_universes_skip_params(ctor_ty: KExpr, n_params: G, ind_level: KLevel,
                                        types: List‹KExpr›,
                                        top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match n_params {
      0 => check_field_universes_inner(ctor_ty, ind_level, types, top, addrs),
      _ =>
        match load(ctor_ty) {
          KExprNode.Forall(dom, body) =>
            let types2 = store(ListNode.Cons(dom, types));
            check_field_universes_skip_params(body, n_params - 1, ind_level, types2, top, addrs),
        },
    }
  }

  fn check_field_universes_inner(ty: KExpr, ind_level: KLevel,
                                  types: List‹KExpr›,
                                  top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let dom_level = k_ensure_sort(dom, types, top, addrs);
        let ok = level_leq(dom_level, ind_level);
        assert_eq!(ok, 1);
        let types2 = store(ListNode.Cons(dom, types));
        check_field_universes_inner(body, ind_level, types2, top, addrs),
      _ => (),
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:1702-1830 check_positivity.
  -- Strict positivity: each ctor field's domain must not have any inductive
  -- of `ind_idx`'s mutual block in a negative position (left of an arrow).
  --
  -- For mutual blocks, the initial positivity context is the full set of
  -- peer inductive idxs (derived via block_addr). Nested inductives are
  -- handled by augment_block_idxs walking ctor bodies recursively.
  fn check_positivity(ctor_ty: KExpr, n_params: G, ind_idx: G,
                      types: List‹KExpr›,
                      top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    let pair = peel_n_foralls_with_types(ctor_ty, n_params, types);
    match pair {
      (body, types_after) =>
        let block_idxs = derive_block_member_idxs(ind_idx, top);
        check_positivity_fields(body, block_idxs, types_after, top, addrs),
    }
  }

  fn peel_n_foralls_tolerant(e: KExpr, n: G) -> KExpr {
    match n {
      0 => e,
      _ =>
        match load(e) {
          KExprNode.Forall(_, body) => peel_n_foralls_tolerant(body, n - 1),
          _ => e,
        },
    }
  }

  -- Like `peel_n_foralls_tolerant` but accumulates each binder's domain into
  -- the types context so subsequent WHNF calls have the right local context.
  fn peel_n_foralls_with_types(e: KExpr, n: G, types: List‹KExpr›) -> (KExpr, List‹KExpr›) {
    match n {
      0 => (e, types),
      _ =>
        match load(e) {
          KExprNode.Forall(dom, body) =>
            let types2 = store(ListNode.Cons(dom, types));
            peel_n_foralls_with_types(body, n - 1, types2),
          _ => (e, types),
        },
    }
  }

  fn check_positivity_fields(ty: KExpr, block_idxs: List‹G›,
                             types: List‹KExpr›,
                             top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        check_positivity_aug(dom, block_idxs, types, top, addrs);
        let types2 = store(ListNode.Cons(dom, types));
        check_positivity_fields(body, block_idxs, types2, top, addrs),
      _ => (),
    }
  }

  -- Mirror src/ix/kernel/inductive.rs:1741-1850. WHNF `dom` first so that
  -- ctor-field types written via reducible defs (e.g. `constType (n α) (n α)`,
  -- `id Sort`) collapse to their underlying inductive head before we
  -- classify them as block / nested / non-inductive.
  fn check_positivity_aug(dom: KExpr, block_idxs: List‹G›,
                           types: List‹KExpr›,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match expr_mentions_any_idx(dom, block_idxs) {
      0 => (),
      _ =>
        let dom_w = whnf(dom, types, top, addrs);
        match load(dom_w) {
          KExprNode.Forall(inner_dom, inner_body) =>
            assert_eq!(expr_mentions_any_idx(inner_dom, block_idxs), 0);
            let types2 = store(ListNode.Cons(inner_dom, types));
            check_positivity_aug(inner_body, block_idxs, types2, top, addrs),
          _ =>
            match collect_spine(dom_w) {
              (head, args) =>
                match load(head) {
                  KExprNode.Const(idx, _) =>
                    match list_contains_g(block_idxs, idx) {
                      1 => (),
                      0 =>
                        -- Nested: idx must be an Inductive in top. Mirror
                        -- src/ix/kernel/inductive.rs:1781-1784: anything
                        -- else (Defn/Thm/Axio/etc.) is "not a valid
                        -- inductive app".
                        let ci = load(list_lookup(top, idx));
                        match ci {
                          KConstantInfo.Induct(_, _, n_params, _, ctor_indices, _, ext_block_addr) =>
                            let after_params = list_drop(args, n_params);
                            assert_eq!(list_any_mentions(after_params, block_idxs), 0);
                            let aug = augment_block_idxs(block_idxs, ext_block_addr, top);
                            check_ctors_positivity(ctor_indices, args, aug, top, addrs),
                          _ =>
                            assert_eq!(0, 1);
                            (),
                        },
                    },
                  _ =>
                    assert_eq!(0, 1);
                    (),
                },
            },
        },
    }
  }

  fn list_contains_g(xs: List‹G›, target: G) -> G {
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(x, rest) =>
        match x - target {
          0 => 1,
          _ => list_contains_g(rest, target),
        },
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs fn computed_is_rec. Ixon no longer
  -- stores the recr flag; is_rec is computed on demand from constructor
  -- structure. Aiur memoization is the is_rec_cache (keyed on induct_idx);
  -- no cycle-breaking needed because `compute_is_rec` is structural (no
  -- whnf), unlike the Rust version.
  fn computed_is_rec_ind(induct_idx: G, top: List‹&KConstantInfo›) -> G {
    let ci = load(list_lookup(top, induct_idx));
    match ci {
      KConstantInfo.Induct(_, _, n_params, _, ctor_indices, _, _) =>
        let block_idxs = derive_block_member_idxs(induct_idx, top);
        compute_is_rec(ctor_indices, n_params, block_idxs, top),
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs fn compute_is_rec.
  -- Compute is_rec by scanning each ctor's field domains (post n_params
  -- peeling) for any reference to a block member's idx.
  -- Returns 1 iff at least one field domain mentions a block_idx.
  fn compute_is_rec(ctors: List‹G›, n_params: G, block_idxs: List‹G›,
                    top: List‹&KConstantInfo›) -> G {
    match load(ctors) {
      ListNode.Nil => 0,
      ListNode.Cons(ctor_idx, rest) =>
        let ctor_ci = load(list_lookup(top, ctor_idx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _) =>
            let after_params = peel_n_foralls_tolerant(ctor_ty, n_params);
            match scan_fields_for_block_ref(after_params, block_idxs) {
              1 => 1,
              0 => compute_is_rec(rest, n_params, block_idxs, top),
            },
          _ => compute_is_rec(rest, n_params, block_idxs, top),
        },
    }
  }

  fn scan_fields_for_block_ref(ty: KExpr, block_idxs: List‹G›) -> G {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match expr_mentions_any_idx(dom, block_idxs) {
          1 => 1,
          0 => scan_fields_for_block_ref(body, block_idxs),
        },
      _ => 0,
    }
  }

  fn expr_mentions_any_idx(e: KExpr, idxs: List‹G›) -> G {
    match load(e) {
      KExprNode.BVar(_) => 0,
      KExprNode.Srt(_) => 0,
      KExprNode.Const(idx, _) => list_contains_g(idxs, idx),
      KExprNode.App(f, a) =>
        let fm = expr_mentions_any_idx(f, idxs);
        match fm {
          1 => 1,
          0 => expr_mentions_any_idx(a, idxs),
        },
      KExprNode.Lam(t, b) =>
        let tm = expr_mentions_any_idx(t, idxs);
        match tm {
          1 => 1,
          0 => expr_mentions_any_idx(b, idxs),
        },
      KExprNode.Forall(t, b) =>
        let tm = expr_mentions_any_idx(t, idxs);
        match tm {
          1 => 1,
          0 => expr_mentions_any_idx(b, idxs),
        },
      KExprNode.Let(t, v, b) =>
        let tm = expr_mentions_any_idx(t, idxs);
        match tm {
          1 => 1,
          0 =>
            let vm = expr_mentions_any_idx(v, idxs);
            match vm {
              1 => 1,
              0 => expr_mentions_any_idx(b, idxs),
            },
        },
      KExprNode.Lit(_) => 0,
      KExprNode.Proj(_, _, e1) => expr_mentions_any_idx(e1, idxs),
    }
  }

  fn list_any_mentions(es: List‹KExpr›, idxs: List‹G›) -> G {
    match load(es) {
      ListNode.Nil => 0,
      ListNode.Cons(e, rest) =>
        let m = expr_mentions_any_idx(e, idxs);
        match m {
          1 => 1,
          0 => list_any_mentions(rest, idxs),
        },
    }
  }

  -- Augment block_idxs with the indices of all Inducts in `top` that share
  -- `ext_block_addr` (so the ext Induct's own block becomes part of the
  -- positivity context).
  fn augment_block_idxs(block_idxs: List‹G›, ext_block_addr: Addr,
                         top: List‹&KConstantInfo›) -> List‹G› {
    augment_walk(block_idxs, ext_block_addr, top, 0)
  }

  fn augment_walk(block_idxs: List‹G›, ext_block_addr: Addr,
                   consts: List‹&KConstantInfo›, idx: G) -> List‹G› {
    match load(consts) {
      ListNode.Nil => block_idxs,
      ListNode.Cons(&ci, rest) =>
        match ci {
          KConstantInfo.Induct(_, _, _, _, _, _, ba) =>
            let same = address_eq(ba, ext_block_addr);
            let nonzero = 1 - address_eq(ext_block_addr, store([0u8; 32]));
            let already = list_contains_g(block_idxs, idx);
            let add = same * nonzero * (1 - already);
            match add {
              1 =>
                let new_idxs = store(ListNode.Cons(idx, block_idxs));
                augment_walk(new_idxs, ext_block_addr, rest, idx + 1),
              0 =>
                augment_walk(block_idxs, ext_block_addr, rest, idx + 1),
            },
          _ =>
            augment_walk(block_idxs, ext_block_addr, rest, idx + 1),
        },
    }
  }

  -- Walk ext inductive's ctors. For each, apply substituted-positivity check
  -- on field types via `check_positivity_aug`. Param substitution is implicit
  -- — ext ctors reference params via BVar; we treat ext's params as lifted
  -- block_idxs since the nested ext fields can mention any of those.
  -- Simplification: walk ctor body fields directly; their refs to ext
  -- params correspond positionally to args[0..n_params] which are checked
  -- transitively when augmented. Sound for direct nested cases.
  fn check_ctors_positivity(ctor_indices: List‹G›, args: List‹KExpr›,
                            aug: List‹G›, top: List‹&KConstantInfo›,
                            addrs: List‹Addr›) {
    match load(ctor_indices) {
      ListNode.Nil => (),
      ListNode.Cons(ctor_idx, rest) =>
        let ctor_ci = load(list_lookup(top, ctor_idx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, n_params, _, _) =>
            let pair = peel_n_foralls_with_types(ctor_ty, n_params, store(ListNode.Nil));
            match pair {
              (body, types_after) =>
                check_positivity_fields_aug(body, aug, types_after, top, addrs);
                check_ctors_positivity(rest, args, aug, top, addrs),
            },
          _ => check_ctors_positivity(rest, args, aug, top, addrs),
        },
    }
  }

  fn check_positivity_fields_aug(ty: KExpr, aug: List‹G›,
                                  types: List‹KExpr›,
                                  top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        check_positivity_aug(dom, aug, types, top, addrs);
        let types2 = store(ListNode.Cons(dom, types));
        check_positivity_fields_aug(body, aug, types2, top, addrs),
      _ => (),
    }
  }

  -- Returns 1 if `e` contains any Const(ind_idx, _), 0 otherwise.
  fn expr_mentions_idx(e: KExpr, ind_idx: G) -> G {
    match load(e) {
      KExprNode.BVar(_) => 0,
      KExprNode.Srt(_) => 0,
      KExprNode.Const(idx, _) =>
        match idx - ind_idx {
          0 => 1,
          _ => 0,
        },
      KExprNode.App(f, a) =>
        g_or(expr_mentions_idx(f, ind_idx), expr_mentions_idx(a, ind_idx)),
      KExprNode.Lam(t, b) =>
        g_or(expr_mentions_idx(t, ind_idx), expr_mentions_idx(b, ind_idx)),
      KExprNode.Forall(t, b) =>
        g_or(expr_mentions_idx(t, ind_idx), expr_mentions_idx(b, ind_idx)),
      KExprNode.Let(t, v, b) =>
        g_or(expr_mentions_idx(t, ind_idx),
             g_or(expr_mentions_idx(v, ind_idx), expr_mentions_idx(b, ind_idx))),
      KExprNode.Lit(_) => 0,
      KExprNode.Proj(_, _, e1) => expr_mentions_idx(e1, ind_idx),
    }
  }

  -- ============================================================================
  -- Canonical recursor type generation (solo / mutual / nested-aux)
  --
  -- Mirror: src/ix/kernel/inductive.rs::build_motive_type_flat (line 2475+).
  -- For non-aux members (is_aux=0): peel own_params with BVar refs to
  -- recursor's outer params. For aux members (is_aux=1): substitute first
  -- |spec_params| with the concrete spec_params lifted to the current depth.
  -- n_rec_params is the block-shared param count; univ_offset is 0 for
  -- Prop-targeting inductives, 1 for large eliminators (motive output univ
  -- added at position 0).
  -- ============================================================================

  -- Build motive type:
  --   forall (i_0 : I_0_ty) ... (i_M : I_M_ty),
  --   forall (major : Indc.{occurrence_us} params indices),
  --   Sort elim_level
  --
  -- Where:
  --   * params come from peeling n_params Foralls off ind_ty, substituting
  --     each binder with BVar(n_rec_params - 1 - j) (recursor outer-scope
  --     param refs);
  --   * occurrence_us = [Param(univ_offset), ..., Param(univ_offset + ind_lvls - 1)];
  --   * elim_level is Param(0) for large eliminators, Zero for Prop.
  -- Mirror: src/ix/kernel/inductive.rs:2128-2205 is_large_eliminator.
  -- Returns 1 if recursor for this Indc can target any universe (i.e.
  -- gets a motive output univ param), 0 if must target Prop.
  --
  -- Cases (mirrors lean4lean):
  --   1. Result level non-zero → always large.
  --   2. Result is Prop AND 0 ctors (Empty/False) → large.
  --   3. Result is Prop AND single ctor AND 0 fields → large.
  --   4. Result is Prop AND single ctor AND all fields are Prop-typed
  --      → large (subsingleton). Covers And/Eq/Acc/Iff/etc.
  --      (Approximation of Rust's full check: all non-trivial fields
  --      must appear in return args; conservative when some field is
  --      Type-typed since we then return 0 = not large.)
  --   5. Otherwise (multiple ctors in Prop) → not large.
  fn is_large_eliminator(result_level: KLevel,
                         ctor_indices: List‹G›,
                         top: List‹&KConstantInfo›,
                         addrs: List‹Addr›) -> G {
    let nz = level_is_not_zero(result_level);
    match nz {
      1 => 1,
      0 =>
        let n_ctors = list_length(ctor_indices);
        match n_ctors {
          0 => 1,
          1 =>
            let ctor_idx = list_lookup(ctor_indices, 0);
            let ctor_ci = load(list_lookup(top, ctor_idx));
            match ctor_ci {
              KConstantInfo.Ctor(_, ctor_ty, _, _, n_params, n_fields, _) =>
                match n_fields {
                  0 => 1,
                  _ =>
                    check_large_prop_ctor(ctor_ty, n_params, n_fields,
                                          store(ListNode.Nil), top, addrs),
                },
            },
          _ => 0,
        },
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:2148-2200 large-elim check on Prop
  -- single-ctor inductive. Walk past `n_params` Foralls (skipping params),
  -- then walk `n_fields` Foralls collecting de Bruijn indices of data fields
  -- (those whose domain has sort != 0). Body after walk is the ctor's return
  -- type; check each data field's BVar appears in the return-type's spine
  -- args. If all do → large eliminator.
  fn check_large_prop_ctor(ty: KExpr, n_params: G, n_fields: G,
                           types: List‹KExpr›, top: List‹&KConstantInfo›,
                           addrs: List‹Addr›) -> G {
    match n_params {
      0 =>
        check_large_walk_fields(ty, n_fields, 0, types, top, addrs,
                                store(ListNode.Nil)),
      _ =>
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            let inner = store(ListNode.Cons(dom, types));
            check_large_prop_ctor(body, n_params - 1, n_fields, inner, top, addrs),
          _ => 0,
        },
    }
  }

  -- Walk `n_fields` Foralls, threading list of data-field BVars (de Bruijn
  -- indices in the post-walk ret context). After walk, collect ret spine
  -- args and verify every data BVar appears.
  fn check_large_walk_fields(ty: KExpr, n_fields: G, field_idx: G,
                              types: List‹KExpr›, top: List‹&KConstantInfo›,
                              addrs: List‹Addr›,
                              data_bvars: List‹G›) -> G {
    match n_fields - field_idx {
      0 =>
        match collect_spine(ty) {
          (_, args) => all_bvars_in_args(data_bvars, args),
        },
      _ =>
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            let lvl = k_ensure_sort(dom, types, top, addrs);
            let is_data = 1 - level_equal(lvl, store(KLevelNode.Zero));
            let bvar_idx = n_fields - 1 - field_idx;
            let new_bvars = match is_data {
              0 => data_bvars,
              _ => store(ListNode.Cons(bvar_idx, data_bvars)),
            };
            let inner = store(ListNode.Cons(dom, types));
            check_large_walk_fields(body, n_fields, field_idx + 1, inner, top, addrs,
                                     new_bvars),
          _ => 0,
        },
    }
  }

  -- Returns 1 iff every BVar idx in `bvars` appears in `args` (as a syntactic
  -- BVar at the ret-binder depth).
  fn all_bvars_in_args(bvars: List‹G›, args: List‹KExpr›) -> G {
    match load(bvars) {
      ListNode.Nil => 1,
      ListNode.Cons(b, rest) =>
        match args_contain_bvar(args, b) {
          0 => 0,
          1 => all_bvars_in_args(rest, args),
        },
    }
  }

  -- Returns 1 if any element of `args` is syntactically `BVar(target)`.
  fn args_contain_bvar(args: List‹KExpr›, target: G) -> G {
    match load(args) {
      ListNode.Nil => 0,
      ListNode.Cons(a, rest) =>
        match load(a) {
          KExprNode.BVar(i) =>
            match i - target {
              0 => 1,
              _ => args_contain_bvar(rest, target),
            },
          _ => args_contain_bvar(rest, target),
        },
    }
  }

  -- Build motive type for a flat block member.
  -- is_aux=0 (original): peel n_own_params subst with BVar(n_rec_params-1-j).
  -- is_aux=1 (aux for nested ext): peel ext.n_params; substitute first
  --   spec_params.len() with spec_params[j] (lifted to current depth=0,
  --   which equals identity when spec_params live in recursor-param frame),
  --   the rest with BVar(n_rec_params-1-j).
  -- Major: aux applies spec_params lifted by n_indices; non-aux applies
  -- recursor-param BVars.
  fn build_motive_type_flat(ind_idx: G, ind_ty: KExpr,
                            n_own_params: G, n_indices: G,
                            occurrence_us: List‹KLevel›,
                            elim_level: KLevel,
                            n_rec_params: G,
                            is_aux: G, spec_params: List‹KExpr›) -> KExpr {
    let ind_ty_inst = expr_inst_levels(ind_ty, occurrence_us);
    let after_params = peel_motive_params_subst(ind_ty_inst, n_own_params, n_rec_params,
                                          is_aux, spec_params, 0);
    let index_doms = collect_index_doms(after_params, n_indices);
    let head = store(KExprNode.Const(ind_idx, occurrence_us));
    let with_args = build_major_args_for_member(head, n_rec_params, n_indices,
                                                 is_aux, spec_params);
    let major_ty = build_major_indices(with_args, n_indices, 0);
    let sort_e = store(KExprNode.Srt(elim_level));
    let with_major = store(KExprNode.Forall(major_ty, sort_e));
    wrap_foralls(with_major, index_doms)
  }

  -- For aux: apply spec_params (each lifted by depth=n_indices) to head.
  -- For non-aux: apply n_rec_params recursor-param BVars to head.
  fn build_major_args_for_member(head: KExpr, n_rec_params: G, depth: G,
                                  is_aux: G, spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => build_major_params(head, n_rec_params, depth, 0),
      _ => apply_spec_params_lifted(head, spec_params, depth),
    }
  }

  fn apply_spec_params_lifted(head: KExpr, spec_params: List‹KExpr›,
                              depth: G) -> KExpr {
    match load(spec_params) {
      ListNode.Nil => head,
      ListNode.Cons(sp, rest) =>
        let lifted = expr_lift(sp, depth, 0);
        apply_spec_params_lifted(store(KExprNode.App(head, lifted)), rest, depth),
    }
  }

  -- Peel n Foralls; for each binder j substitute per is_aux:
  --   non-aux: BVar(n_rec_params - 1 - j).
  --   aux: spec_params[j] when j < |spec_params|, else BVar(n_rec_params - 1 - j).
  fn peel_motive_params_subst(ty: KExpr, n: G, n_rec_params: G,
                        is_aux: G, spec_params: List‹KExpr›, j: G) -> KExpr {
    match n {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            let p = subst_param_for(j, n_rec_params, is_aux, spec_params);
            let body_substed = expr_inst1(body, p, 0);
            peel_motive_params_subst(body_substed, n - 1, n_rec_params,
                              is_aux, spec_params, j + 1),
        },
    }
  }

  fn subst_param_for(j: G, n_rec_params: G, is_aux: G,
                      spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => store(KExprNode.BVar((n_rec_params - 1) - j)),
      _ =>
        let len = list_length(spec_params);
        let lt = u32_less_than(j, len);
        match lt {
          1 => list_lookup(spec_params, j),
          _ => store(KExprNode.BVar((n_rec_params - 1) - j)),
        },
    }
  }

  -- Peel ctor's leading own_params. Non-aux: plain peel. Aux: substitute
  -- each with spec_params[j] (or BVar fallback if beyond spec).
  fn peel_rule_ctor_params(ty: KExpr, n: G,
                            is_aux: G, spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => peel_n_foralls(ty, n),
      -- Rule-rhs field doms stay in the natural ctor-body scope (params
      -- directly above): spec_lift = 0, later frame moves happen at the
      -- use sites via list_lift_indices.
      _ => peel_ctor_params_subst(ty, n, 0, 0, 1, spec_params, 0),
    }
  }

  -- Look up Ctor.num_params from top.
  fn ctor_num_params_of(ctor_idx: G, top: List‹&KConstantInfo›) -> G {
    let ci = load(list_lookup(top, ctor_idx));
    match ci {
      KConstantInfo.Ctor(_, _, _, _, num_params, _, _) => num_params,
      _ => 0,
    }
  }

  -- Peel ctor's own_params with depth-aware substitution. For non-aux:
  -- BVar(depth-1-j). For aux: spec_params[j] lifted by `spec_lift`
  -- (binders between the recursor-param frame and the peel point — NOT
  -- `depth`, which counts the params themselves too) when j < |spec|;
  -- BVar(depth-1-j) otherwise.
  fn peel_ctor_params_subst(ty: KExpr, n: G, depth: G, spec_lift: G,
                             is_aux: G, spec_params: List‹KExpr›, j: G) -> KExpr {
    match n {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            let p = ctor_subst_param_for(j, depth, spec_lift, is_aux, spec_params);
            let body_substed = expr_inst1(body, p, 0);
            peel_ctor_params_subst(body_substed, n - 1, depth, spec_lift,
                                    is_aux, spec_params, j + 1),
        },
    }
  }

  fn ctor_subst_param_for(j: G, depth: G, spec_lift: G, is_aux: G,
                           spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => store(KExprNode.BVar((depth - 1) - j)),
      _ =>
        let len = list_length(spec_params);
        let lt = u32_less_than(j, len);
        match lt {
          1 =>
            let sp = list_lookup(spec_params, j);
            expr_lift(sp, spec_lift, 0),
          _ => store(KExprNode.BVar((depth - 1) - j)),
        },
    }
  }

  fn collect_index_doms(ty: KExpr, n: G) -> List‹KExpr› {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            store(ListNode.Cons(dom, collect_index_doms(body, n - 1))),
        },
    }
  }

  -- [Param(start), Param(start+1), ..., Param(start+count-1)] as List‹KLevel›.
  fn build_param_lvls_range(start: G, count: G, i: G) -> List‹KLevel› {
    match count - i {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons(
          store(KLevelNode.Param(start + i)),
          build_param_lvls_range(start, count, i + 1))),
    }
  }

  -- Apply head to recursor params: `App(... App(head, BVar(n_rec_params-1+depth)), ...)`.
  -- Each param j is at BVar(n_rec_params - 1 - j + depth) where depth is
  -- the index-binder count above the major position.
  fn build_major_params(head: KExpr, n_rec_params: G, depth: G, j: G) -> KExpr {
    match n_rec_params - j {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(((n_rec_params - 1) - j) + depth));
        build_major_params(store(KExprNode.App(head, v)), n_rec_params, depth, j + 1),
    }
  }

  -- Apply head to indices: `App(... App(head, BVar(n_indices-1)), ...)`.
  -- Index i (0-indexed from outermost) is BVar(n_indices - 1 - i) at the
  -- major's scope.
  fn build_major_indices(head: KExpr, n_indices: G, i: G) -> KExpr {
    match n_indices - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar((n_indices - 1) - i));
        build_major_indices(store(KExprNode.App(head, v)), n_indices, i + 1),
    }
  }

  -- Wrap body in foralls outside-in: doms = [d0, d1, ..., dM] →
  -- `forall (_ : d0), forall (_ : d1), ..., forall (_ : dM), body`.
  fn wrap_foralls(body: KExpr, doms: List‹KExpr›) -> KExpr {
    match load(doms) {
      ListNode.Nil => body,
      ListNode.Cons(dom, rest) =>
        store(KExprNode.Forall(dom, wrap_foralls(body, rest))),
    }
  }

  -- ============================================================================
  -- build_minor_at_depth (flat-aware: solo / mutual / nested-aux)
  --
  -- Mirror: src/ix/kernel/inductive.rs:2596-2806.
  -- Builds the minor binder type for a single ctor, including IHs for
  -- recursive fields. Forall-wrapped recursive fields (e.g.
  -- `(Nat → Foo) → Foo`) are handled via `is_rec_field` peeling leading
  -- foralls + `build_ih_doms` wrapping IH body in matching foralls.
  -- For aux ctors (is_aux=1): peel ext.n_params with spec_params subst.
  -- Motive offset = `motive_base + self_mem_idx` for the owning member.
  -- ============================================================================
  -- `self_mem_idx` = this member's POSITION in flat (not resolved from
  -- ind_idx: two aux entries can share the same base const idx with
  -- different spec_params, and an idx lookup would alias the second
  -- member's motive to the first's).
  fn build_minor_at_depth(ind_idx: G, ctor_idx: G, ctor_ty: KExpr,
                          is_aux: G, spec_params: List‹KExpr›,
                          occurrence_us: List‹KLevel›,
                          flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                          flat_idxs: List‹G›,
                          flat_own_params: List‹G›,
                          n_rec_params: G, n_motives: G, prev_minors: G,
                          motive_base: G, self_mem_idx: G,
                          top: List‹&KConstantInfo›, addrs: List‹Addr›) -> KExpr {
    let ctor_ty_inst = expr_inst_levels(ctor_ty, occurrence_us);
    let minor_saved = n_rec_params + n_motives + prev_minors;
    -- Peel ctor's own_params. For non-aux: n_own_params == n_rec_params, all
    -- substitute with BVar(minor_saved-1-j). For aux: n_own_params == ext.n_params;
    -- first |spec_params| substitute with spec_params[j] lifted by
    -- below_params, the rest with BVar(minor_saved-1-j).
    let n_own_params = ctor_num_params_of(ctor_idx, top);
    -- Binders between the recursor-param frame and this minor's start:
    -- the motives and previous minors. Spec_params lift by this amount
    -- (both when substituted into aux ctor params and when matched by
    -- is_rec_field).
    let below_params = n_motives + prev_minors;
    let after_params = peel_ctor_params_subst(ctor_ty_inst, n_own_params,
                                               minor_saved, below_params,
                                               is_aux, spec_params, 0);
    let walk = walk_fields_classify(after_params, flat, store(ListNode.Nil),
                                     store(ListNode.Nil), store(ListNode.Nil),
                                     store(ListNode.Nil), top, addrs, 0,
                                     below_params);
    match walk {
      (field_doms, rec_indices, rec_member_idxs, ret_ty) =>
        let n_fields = list_length(field_doms);
        let n_ihs = list_length(rec_indices);
        let n_binders = n_fields + n_ihs;
        let depth_now = minor_saved + n_binders;
        let ret_pair = collect_spine(ret_ty);
        match ret_pair {
          (_ret_head, ret_args) =>
            -- Drop n_own_params from ret to expose indices.
            let ret_indices = list_drop(ret_args, n_own_params);
            let ret_indices_lifted = list_lift_each(ret_indices, n_ihs, 0);
            let motive_var = (depth_now - 1) - (motive_base + self_mem_idx);
            let motive_ref = store(KExprNode.BVar(motive_var));
            let with_indices = apply_spine(motive_ref, ret_indices_lifted);
            let ctor_head = store(KExprNode.Const(ctor_idx, occurrence_us));
            -- For non-aux: apply n_rec_params recursor-param BVars.
            -- For aux: apply spec_params lifted to body scope (depth_now-1+1 = depth_now).
            let with_params = build_ctor_app_params(ctor_head, n_own_params,
                                                     n_rec_params, depth_now,
                                                     is_aux, spec_params);
            let ctor_app = build_apply_field_bvars(with_params, n_fields, n_binders, 0);
            let conclusion = store(KExprNode.App(with_indices, ctor_app));
            let ih_doms = build_ih_doms(rec_indices, rec_member_idxs, field_doms,
                                        flat_own_params, motive_base, n_fields,
                                        minor_saved, store(ListNode.Nil), top, addrs, 0);
            let with_ihs = wrap_foralls(conclusion, ih_doms);
            wrap_foralls(with_ihs, field_doms),
        },
    }
  }

  -- Apply ctor head with its own_params. Non-aux: BVar refs to recursor
  -- params (depth_now-1 down to depth_now-n_rec_params). Aux: spec_params
  -- lifted from the recursor-param frame by the binders below the params
  -- (depth_now counts the params themselves; subtract them).
  fn build_ctor_app_params(head: KExpr, n_own_params: G, n_rec_params: G,
                           depth_now: G,
                           is_aux: G, spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => build_apply_bvars_decreasing(head, n_rec_params, depth_now - 1, 0),
      _ => apply_spec_params_lifted(head, spec_params, depth_now - n_rec_params),
    }
  }

  -- Peel n Foralls; substitute each binder with `BVar(depth - 1 - j)`.
  fn peel_n_subst_at_depth(ty: KExpr, n: G, depth: G, j: G) -> KExpr {
    match n {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            let p = store(KExprNode.BVar((depth - 1) - j));
            let body_substed = expr_inst1(body, p, 0);
            peel_n_subst_at_depth(body_substed, n - 1, depth, j + 1),
        },
    }
  }

  -- Walk Foralls of `ty` collecting (field_doms, rec_field_indices, ret_ty).
  -- A field is recursive (direct case) when its spine head is Const(ind_idx).
  -- Builds accumulators with O(1) cons (prepend) and reverses once at end —
  -- O(F) total vs O(F²) with snoc.
  fn walk_fields_classify(ty: KExpr, flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                          doms_acc: List‹KExpr›, rec_acc: List‹G›,
                          rec_mem_acc: List‹G›,
                          types: List‹KExpr›,
                          top: List‹&KConstantInfo›, addrs: List‹Addr›,
                          fidx: G, spec_lift_by: G)
                          -> (List‹KExpr›, List‹G›, List‹G›, KExpr) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let r = is_rec_field(dom, flat, types, top, addrs, spec_lift_by);
        let new_doms = store(ListNode.Cons(dom, doms_acc));
        let types2 = store(ListNode.Cons(dom, types));
        match r {
          (1, mem_idx) =>
            let new_rec = store(ListNode.Cons(fidx, rec_acc));
            let new_mem = store(ListNode.Cons(mem_idx, rec_mem_acc));
            walk_fields_classify(body, flat, new_doms, new_rec, new_mem,
                                 types2, top, addrs, fidx + 1, spec_lift_by),
          _ =>
            walk_fields_classify(body, flat, new_doms, rec_acc, rec_mem_acc,
                                 types2, top, addrs, fidx + 1, spec_lift_by),
        },
      _ => (list_reverse(doms_acc), list_reverse(rec_acc), list_reverse(rec_mem_acc), ty),
    }
  }

  -- Derive the list of block-member indices for a recursor's parent ind.
  -- Solo (ind's block_addr = [0;32]) → `[ind_idx]`. Otherwise walks `top`
  -- collecting all Inducts sharing the block_addr in positional order.
  fn derive_block_member_idxs(ind_idx: G, top: List‹&KConstantInfo›) -> List‹G› {
    let ci = load(list_lookup(top, ind_idx));
    match ci {
      KConstantInfo.Induct(_, _, _, _, _, _, block_addr) =>
        match address_eq(block_addr, store([0u8; 32])) {
          1 => store(ListNode.Cons(ind_idx, store(ListNode.Nil))),
          0 => collect_block_members(block_addr, top, 0),
        },
      _ => store(ListNode.Cons(ind_idx, store(ListNode.Nil))),
    }
  }

  fn collect_block_members(block_addr: Addr,
                           consts: List‹&KConstantInfo›, idx: G) -> List‹G› {
    match load(consts) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(&ci, rest) =>
        match ci {
          KConstantInfo.Induct(_, _, _, _, _, _, ba) =>
            match address_eq(ba, block_addr) {
              1 => store(ListNode.Cons(idx, collect_block_members(block_addr, rest, idx + 1))),
              0 => collect_block_members(block_addr, rest, idx + 1),
            },
          _ => collect_block_members(block_addr, rest, idx + 1),
        },
    }
  }

  -- Returns 1 iff idx ≠ ind_idx but Inducts at idx and ind_idx share the
  -- same non-[0;32] block_addr. Used to classify peer/aux refs in block
  -- as recursive for IH building.
  fn is_in_same_block(idx: G, ind_idx: G, top: List‹&KConstantInfo›) -> G {
    let i_ci = load(list_lookup(top, ind_idx));
    match i_ci {
      KConstantInfo.Induct(_, _, _, _, _, _, ind_ba) =>
        match address_eq(ind_ba, store([0u8; 32])) {
          1 => 0,
          0 =>
            let other_ci = load(list_lookup(top, idx));
            match other_ci {
              KConstantInfo.Induct(_, _, _, _, _, _, other_ba) =>
                address_eq(other_ba, ind_ba),
              _ => 0,
            },
        },
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:2968-3019 fn is_rec_field.
  -- Returns (is_rec, member_local_idx) where member_local_idx is the position
  -- within `flat` of the matching entry (0 for direct member). Returns (0, 0)
  -- if not recursive. WHNFs the per-field body so that ctor field types written
  -- via reducible defs collapse to expose the underlying inductive head. The
  -- match key is (head_const_idx, spine_arg_prefix ≡ flat.spec_params) — const
  -- idx alone is not enough because a nested aux (e.g. `List Lean.Syntax`)
  -- shares the base ind's idx with unrelated occurrences (e.g. `List
  -- Preresolved`); using idx alone would false-positive the unrelated field
  -- as recursive and inject a spurious IH binder.
  -- `spec_lift_by` = binders between the recursor-param frame (where
  -- flat spec_params live) and the start of the caller's field walk;
  -- the field's own walk depth (`list_length(types)`) is added here.
  -- Mirror: Rust's explicit `spec_params_lift_by` (inductive.rs:2972,
  -- see the historical note there — guessing the lift from local depth
  -- breaks one of build_minor_at_depth / build_rule_rhs).
  fn is_rec_field(dom: KExpr, flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                   types: List‹KExpr›, top: List‹&KConstantInfo›,
                   addrs: List‹Addr›, spec_lift_by: G) -> (G, G) {
    match peel_leading_foralls(dom) {
      (doms, body) =>
        let inner_types = list_concat(list_reverse(doms), types);
        let body_w = whnf(body, inner_types, top, addrs);
        match collect_spine(body_w) {
          (head, spine_args) =>
            match load(head) {
              KExprNode.Const(idx, _) =>
                let lift = spec_lift_by + list_length(types);
                find_flat_member_match(flat, idx, spine_args, 0, lift),
              _ => (0, 0),
            },
        },
    }
  }

  -- Walk `flat`; return (1, i) at the first entry whose idx == head_idx AND
  -- whose spec_params structurally match the leading `|spec_params|` entries
  -- of the field's spine args. Original members have spec_params=[] so any
  -- field whose head is the original ind matches. Auxes carry their concrete
  -- occurrence, so only fields applied to that exact occurrence match.
  fn find_flat_member_match(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                             head_idx: G, spine_args: List‹KExpr›,
                             i: G, spec_lift_by: G) -> (G, G) {
    match load(flat) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(entry, rest) =>
        match entry {
          (fidx, _, fsps, _) =>
            match fidx - head_idx {
              0 =>
                match spine_prefix_eq(spine_args, fsps, spec_lift_by) {
                  1 => (1, i),
                  _ => find_flat_member_match(rest, head_idx, spine_args, i + 1,
                                              spec_lift_by),
                },
              _ => find_flat_member_match(rest, head_idx, spine_args, i + 1,
                                          spec_lift_by),
            },
        },
    }
  }

  -- Structural prefix compare: 1 iff `spec_params` (lifted from the
  -- recursor-param frame to the caller's depth) is a prefix of
  -- `spine_args` under `kexpr_struct_eq`. Empty spec_params always
  -- matches.
  fn spine_prefix_eq(spine_args: List‹KExpr›, spec_params: List‹KExpr›,
                     spec_lift_by: G) -> G {
    match load(spec_params) {
      ListNode.Nil => 1,
      ListNode.Cons(sp, sps_rest) =>
        match load(spine_args) {
          ListNode.Nil => 0,
          ListNode.Cons(sa, sa_rest) =>
            match kexpr_struct_eq(sa, expr_lift(sp, spec_lift_by, 0)) {
              1 => spine_prefix_eq(sa_rest, sps_rest, spec_lift_by),
              _ => 0,
            },
        },
    }
  }

  -- Find target's index within block_member_idxs. (1, idx) if found else (0, 0).
  fn find_member_local_idx(idxs: List‹G›, target: G, i: G) -> (G, G) {
    match load(idxs) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(x, rest) =>
        match x - target {
          0 => (1, i),
          _ => find_member_local_idx(rest, target, i + 1),
        },
    }
  }

  fn peel_leading_foralls(ty: KExpr) -> (List‹KExpr›, KExpr) {
    let pair = peel_leading_foralls_acc(ty, store(ListNode.Nil));
    match pair {
      (rev_acc, body) => (list_reverse(rev_acc), body),
    }
  }

  -- Builds doms in reverse via O(1) cons; caller reverses once.
  fn peel_leading_foralls_acc(ty: KExpr, acc: List‹KExpr›) -> (List‹KExpr›, KExpr) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        peel_leading_foralls_acc(body, store(ListNode.Cons(dom, acc))),
      _ => (acc, ty),
    }
  }

  -- Apply head to xs from outermost: x_0 = BVar(n_xs - 1), ..., x_{n-1} = BVar(0).
  fn build_apply_xs(head: KExpr, n_xs: G, i: G) -> KExpr {
    match n_xs - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar((n_xs - 1) - i));
        build_apply_xs(store(KExprNode.App(head, v)), n_xs, i + 1),
    }
  }

  fn list_lift_each(es: List‹KExpr›, shift: G, cutoff: G) -> List‹KExpr› {
    match load(es) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(e, rest) =>
        store(ListNode.Cons(expr_lift(e, shift, cutoff),
                            list_lift_each(rest, shift, cutoff))),
    }
  }

  -- Apply head to BVars at descending positions: `App(... App(head, BVar(start)), BVar(start-1)), ...`
  -- Used for ctor params (BVar refs to recursor's outer params at depth_now).
  fn build_apply_bvars_decreasing(head: KExpr, n: G, start: G, j: G) -> KExpr {
    match n - j {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - j));
        build_apply_bvars_decreasing(store(KExprNode.App(head, v)), n, start, j + 1),
    }
  }

  -- Apply head to ctor fields: `App(... App(head, BVar(n_binders-1)), BVar(n_binders-2)), ...`
  fn build_apply_field_bvars(head: KExpr, n_fields: G, n_binders: G, i: G) -> KExpr {
    match n_fields - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar((n_binders - 1) - i));
        build_apply_field_bvars(store(KExprNode.App(head, v)), n_fields, n_binders, i + 1),
    }
  }

  -- For each (rec_field_idx, k) pair, build IH dom:
  -- `motive (lifted_idx_args) field_var`
  -- at scope where fields are bound but k IHs already pushed.
  --   depth_at_this_ih = minor_saved + n_fields + k
  --   motive_var = depth_at_this_ih - 1 - motive_base
  --   field_var  = depth_at_this_ih - 1 - (minor_saved + field_idx)
  -- Lift the field's dom by (n_fields - field_idx + k) so its BVars
  -- map into current scope. Then strip first n_rec_params spine args.
  -- Collect first n Forall doms; return (doms, remaining_body).
  fn collect_n_doms(ty: KExpr, n: G) -> (List‹KExpr›, KExpr) {
    let pair = collect_n_doms_acc(ty, n, store(ListNode.Nil));
    match pair {
      (rev_acc, body) => (list_reverse(rev_acc), body),
    }
  }

  fn collect_n_doms_acc(ty: KExpr, n: G, acc: List‹KExpr›) -> (List‹KExpr›, KExpr) {
    match n {
      0 => (acc, ty),
      _ =>
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            collect_n_doms_acc(body, n - 1, store(ListNode.Cons(dom, acc))),
        },
    }
  }

  -- Apply head to indices in conclusion scope.
  -- Index i (0-indexed from outer) at BVar(n_indices - i).
  fn apply_indices_in_conclusion(head: KExpr, n_indices: G, i: G) -> KExpr {
    match n_indices - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(n_indices - i));
        apply_indices_in_conclusion(store(KExprNode.App(head, v)), n_indices, i + 1),
    }
  }

  -- Build per-ctor minor type list. is_aux + spec_params + occ_us control
  -- how the ctor's leading own_params are substituted and what occurrence_us
  -- to use for the ctor head; flat_idxs is used for rec field detection.
  fn build_minor_doms(ctor_indices: List‹G›, ind_idx: G,
                      is_aux: G, spec_params: List‹KExpr›,
                      occurrence_us: List‹KLevel›,
                      flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                      flat_idxs: List‹G›,
                      flat_own_params: List‹G›,
                      n_rec_params: G, n_motives: G,
                      motive_base: G, self_mem_idx: G,
                      top: List‹&KConstantInfo›, addrs: List‹Addr›,
                      prev_minors: G) -> List‹KExpr› {
    match load(ctor_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(ctor_idx, rest) =>
        let ctor_ci = load(list_lookup(top, ctor_idx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _) =>
            let minor = build_minor_at_depth(ind_idx, ctor_idx, ctor_ty,
                                             is_aux, spec_params, occurrence_us,
                                             flat, flat_idxs, flat_own_params,
                                             n_rec_params, n_motives, prev_minors,
                                             motive_base, self_mem_idx, top, addrs);
            let rest_minors = build_minor_doms(rest, ind_idx, is_aux, spec_params,
                                               occurrence_us, flat, flat_idxs,
                                               flat_own_params,
                                               n_rec_params, n_motives,
                                               motive_base, self_mem_idx,
                                               top, addrs, prev_minors + 1);
            store(ListNode.Cons(minor, rest_minors)),
        },
    }
  }

  -- Build motive types for every flat block member. Each member's motive_ty
  -- references shared params (BVar 0..n_rec_params-1) and its own n_indices,
  -- with elim_level + univ_offset shared. Motive j (j>0) lifted by j to
  -- account for the j prior motives bound between params and motive j
  -- (mirror src/ix/kernel/inductive.rs:3074-3082).
  fn build_all_motives(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                       n_params: G,
                       ind_lvls: G, elim_level: KLevel, univ_offset: G,
                       n_rec_params: G,
                       top: List‹&KConstantInfo›) -> List‹KExpr› {
    build_all_motives_walk(flat, n_params, ind_lvls, elim_level,
                            univ_offset, n_rec_params, top, 0)
  }

  fn build_all_motives_walk(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                             n_params: G,
                             ind_lvls: G, elim_level: KLevel, univ_offset: G,
                             n_rec_params: G,
                             top: List‹&KConstantInfo›, j: G) -> List‹KExpr› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (member_idx, is_aux, spec_params, occ_us) =>
            let ci = load(list_lookup(top, member_idx));
            match ci {
              KConstantInfo.Induct(_, m_ind_ty, m_own_params, m_n_indices, _, _, _) =>
                let mt = build_motive_type_flat(member_idx, m_ind_ty, m_own_params,
                                                 m_n_indices, occ_us, elim_level,
                                                 n_rec_params,
                                                 is_aux, spec_params);
                let mt_lifted = expr_lift(mt, j, 0);
                store(ListNode.Cons(mt_lifted,
                  build_all_motives_walk(rest, n_params, ind_lvls, elim_level,
                                          univ_offset, n_rec_params, top, j + 1))),
              _ =>
                build_all_motives_walk(rest, n_params, ind_lvls, elim_level,
                                        univ_offset, n_rec_params, top, j),
            },
        },
    }
  }

  -- Aggregate minor types across all flat block members' ctors. prev_minors
  -- is the count of minors already added from previous members; threaded
  -- through so each minor's depth math is correct. flat carries (ind_idx,
  -- is_aux, spec_params) so aux ctors can substitute spec_params during
  -- their own-param peel.
  fn build_all_minors(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                      flat_idxs: List‹G›, flat_own_params: List‹G›,
                      n_rec_params: G, n_motives: G,
                      ind_lvls: G, univ_offset: G, motive_base: G,
                      top: List‹&KConstantInfo›, addrs: List‹Addr›,
                      prev_minors: G) -> List‹KExpr› {
    build_all_minors_walk(flat, flat, flat_idxs, flat_own_params,
                          n_rec_params, n_motives, ind_lvls, univ_offset,
                          motive_base, top, addrs, prev_minors, 0)
  }

  -- `full_flat` stays pinned to the caller's original flat list so
  -- `is_rec_field` sees every block member for spec_params matching; `flat`
  -- shrinks as we iterate members. Bug guarded against: previously we passed
  -- the shrinking `flat` into `build_minor_doms`, which made later members'
  -- ctor-field classification blind to earlier members.
  fn build_all_minors_walk(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                           full_flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                           flat_idxs: List‹G›, flat_own_params: List‹G›,
                           n_rec_params: G, n_motives: G,
                           ind_lvls: G, univ_offset: G, motive_base: G,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›,
                           prev_minors: G, mem_pos: G) -> List‹KExpr› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (member_idx, is_aux, spec_params, occ_us) =>
            let ci = load(list_lookup(top, member_idx));
            match ci {
              KConstantInfo.Induct(_, _, _, _, m_ctor_indices, _, _) =>
                let m_minors = build_minor_doms(m_ctor_indices, member_idx,
                                                 is_aux, spec_params, occ_us,
                                                 full_flat, flat_idxs,
                                                 flat_own_params,
                                                 n_rec_params, n_motives,
                                                 motive_base, mem_pos,
                                                 top, addrs, prev_minors);
                let added = list_length(m_minors);
                let rest_minors = build_all_minors_walk(rest, full_flat,
                                                    flat_idxs, flat_own_params,
                                                    n_rec_params,
                                                    n_motives, ind_lvls, univ_offset,
                                                    motive_base, top, addrs,
                                                    prev_minors + added, mem_pos + 1);
                list_concat(m_minors, rest_minors),
              _ =>
                build_all_minors_walk(rest, full_flat,
                                  flat_idxs, flat_own_params,
                                  n_rec_params, n_motives, ind_lvls,
                                  univ_offset, motive_base, top, addrs, prev_minors,
                                  mem_pos + 1),
            },
        },
    }
  }

  -- ============================================================================
  -- build_rec_type (flat-aware: solo / mutual / nested-aux)
  --
  -- Mirror: src/ix/kernel/inductive.rs:3027+ build_rec_type.
  -- Assembles full recursor type:
  --
  --   forall (params...),
  --   forall (motive_0 : motive_ty_0) ... forall (motive_{N-1} : motive_ty_{N-1}),
  --   forall (minor_0) ... forall (minor_{M-1}),
  --   forall (indices...),
  --   forall (major : Indc params indices),
  --   motive_self indices major
  --
  -- N motives = |flat| (one per original + nested-aux block member).
  -- M minors = sum of |ctors| across all flat members.
  -- Computes elim_level / univ_offset internally via is_large_eliminator.
  -- `primary_ind_idx` is the canonical block's source for `flat`; `ind_idx`
  -- is self (= primary for solo/mutual; aux ext for nested aux recursors).
  -- ============================================================================
  -- `self_mem_pos` = self's POSITION in the flat block (signature-
  -- resolved by the caller); idx lookup would alias same-idx aux
  -- members.
  fn build_rec_type(ind_idx: G, ind_ty: KExpr, ctor_indices: List‹G›,
                    n_params: G, n_indices: G, ind_lvls: G,
                    self_own_params: G,
                    primary_ind_idx: G, self_mem_pos: G,
                    top: List‹&KConstantInfo›, addrs: List‹Addr›) -> KExpr {
    let result_level = get_result_sort_level(ind_ty, self_own_params + n_indices);
    let is_large = is_large_eliminator(result_level, ctor_indices, top, addrs);
    let elim_level = match is_large {
      1 => store(KLevelNode.Param(0)),
      0 => store(KLevelNode.Zero),
    };
    let univ_offset = is_large;
    let block_member_idxs = derive_block_member_idxs(primary_ind_idx, top);
    let flat = build_flat_block(block_member_idxs, univ_offset, top);
    let flat_idxs = flat_ind_idxs(flat);
    let n_motives = list_length(flat);
    let n_rec_params = n_params;
    let motive_base = n_rec_params;

    -- Use self's concrete occurrence_us for ind_ty inst (so nested aux univ
    -- args match what Lean stored).
    let self_member0 = flat_member_at(flat, self_mem_pos);
    let self_occ_us0 = match self_member0 { (_, _, _, ou) => ou, };
    let ind_ty_inst = expr_inst_levels(ind_ty, self_occ_us0);

    let params_walk = collect_n_doms(ind_ty_inst, n_params);
    match params_walk {
      (param_doms, after_params) =>
        let flat_own_params = flat_own_params_of(flat, top);
        let motive_doms = build_all_motives(flat, n_params,
                                             ind_lvls, elim_level, univ_offset,
                                             n_rec_params, top);

        let minor_doms = build_all_minors(flat, flat_idxs, flat_own_params,
                                           n_rec_params, n_motives,
                                           ind_lvls, univ_offset, motive_base, top, addrs, 0);
        let n_minors = list_length(minor_doms);

        let indices_walk = collect_n_doms(after_params, n_indices);
        match indices_walk {
          (index_doms_raw, _ret_sort) =>
            let index_doms = list_lift_indices(index_doms_raw, n_motives + n_minors, 0);
            let self_mem_idx = self_mem_pos;
            let self_member = flat_member_at(flat, self_mem_idx);
            let self_is_aux = match self_member { (_, ia, _, _) => ia, };
            let self_spec_params = match self_member { (_, _, sp, _) => sp, };
            let self_occ_us = match self_member { (_, _, _, ou) => ou, };
            let head = store(KExprNode.Const(ind_idx, self_occ_us));
            let pre_major_depth = n_rec_params + n_motives + n_minors + n_indices;
            let with_args = build_major_args_for_self(head, n_rec_params,
                                                       pre_major_depth - 1,
                                                       n_motives + n_minors + n_indices,
                                                       self_is_aux, self_spec_params);
            let major_ty = build_major_indices(with_args, n_indices, 0);

            let depth_after_major = pre_major_depth + 1;
            let motive_var = (depth_after_major - 1) - (motive_base + self_mem_idx);
            let motive_ref = store(KExprNode.BVar(motive_var));
            let with_indices = apply_indices_in_conclusion(motive_ref, n_indices, 0);
            let conclusion = store(KExprNode.App(with_indices, store(KExprNode.BVar(0))));

            let with_major = store(KExprNode.Forall(major_ty, conclusion));
            let with_idx_foralls = wrap_foralls(with_major, index_doms);
            let with_minors = wrap_foralls(with_idx_foralls, minor_doms);
            let with_motives = wrap_foralls(with_minors, motive_doms);
            wrap_foralls(with_motives, param_doms),
        },
    }
  }

  -- ============================================================================
  -- build_rule_rhs (flat-aware: solo / mutual / nested-aux, direct case)
  --
  -- Mirror: src/ix/kernel/inductive.rs:3571+ build_rule_rhs.
  -- Builds the RHS of the recursor rule for one ctor:
  --
  --   λ (params...) λ (motives...) λ (minors...) λ (fields...),
  --   minor_i field_0 ... field_{F-1} IH_0 ... IH_R
  --
  -- Where IH_j (direct case for rec field of target member t) =
  --   Const(peer_recs[t], lvls) (params) (motives) (minors) (idx_args) field_j
  --
  -- For aux ctors (is_aux=1): peel ext.n_params with spec_params subst so
  -- field doms become concrete. For non-aux mutual: peer_recs maps each
  -- block member to its own recursor. No post-major args.
  -- ============================================================================
  fn build_rule_rhs(rec_idx: G, ind_idx: G, ctor_idx: G, ctor_ty: KExpr,
                    ctor_minor_index: G,
                    n_params: G, n_motives: G, n_minors: G,
                    ind_lvls: G, univ_offset: G,
                    motive_doms: List‹KExpr›, minor_doms: List‹KExpr›,
                    param_doms: List‹KExpr›, peer_recs: List‹G›,
                    flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                    flat_idxs: List‹G›, flat_own_params: List‹G›,
                    is_aux: G, spec_params: List‹KExpr›,
                    occurrence_us: List‹KLevel›,
                    top: List‹&KConstantInfo›, addrs: List‹Addr›) -> KExpr {
    let rec_lvls_list = build_rec_lvls(ind_lvls + univ_offset, 0);
    let ctor_ty_inst = expr_inst_levels(ctor_ty, occurrence_us);
    -- Peel n_params Foralls without substitution. Field doms collected
    -- by walk live in their natural ctor-body scope: at walk position i,
    -- peer fields 0..i-1 occupy BVar(0..i-1) (stack: latest peer at
    -- BVar(0)) and params occupy BVar(i..i+n_params-1) (auto-shifted by
    -- de Bruijn semantics as walk descends Foralls). Lifts to Lam-type
    -- and body scopes happen at use sites.
    -- Peel ctor's own_params. Non-aux: leave as natural BVars (caller lifts
    -- via list_lift_indices). Aux: substitute with spec_params so field doms
    -- become concrete; at this point, depth=0, fields will be lifted later.
    let n_own_params = ctor_num_params_of(ctor_idx, top);
    let after_params = peel_rule_ctor_params(ctor_ty_inst, n_own_params,
                                              is_aux, spec_params);
    -- Natural ctor-body scope: params sit directly above the walk, so
    -- the spec_params base lift is 0 (only the walk depth applies).
    let walk = walk_fields_classify(after_params, flat, store(ListNode.Nil),
                                     store(ListNode.Nil), store(ListNode.Nil),
                                     store(ListNode.Nil), top, addrs, 0, 0);
    match walk {
      (field_doms, rec_indices, rec_member_idxs, _ret_ty) =>
        let n_fields = list_length(field_doms);
        let n_ihs = list_length(rec_indices);
        -- Body scope: all Lams pushed. depth = n_params + n_motives + n_minors + n_fields.
        let body_depth = n_params + n_motives + n_minors + n_fields;
        -- minor_i at BVar(body_depth - 1 - (n_params + n_motives + ctor_minor_index))
        let minor_var = (body_depth - 1) - (n_params + n_motives + ctor_minor_index);
        let minor_ref = store(KExprNode.BVar(minor_var));
        -- Apply ctor fields: field j at BVar(n_fields - 1 - j)
        let with_fields = build_apply_field_bvars(minor_ref, n_fields, n_fields, 0);
        -- Apply IHs: for each rec field j, build IH using peer_recs[mem_idx]
        let body = apply_ihs(with_fields, rec_indices, rec_member_idxs, field_doms,
                             peer_recs, flat_own_params,
                             n_params, n_motives, n_minors, n_fields,
                             rec_lvls_list, store(ListNode.Nil), top, addrs, 0);
        -- Lift each field_dom (in walk-pos i scope) into its Lam-type
        -- scope: peer refs (BVar < walk_pos i) stay; param refs
        -- (BVar >= i) lift by n_motives + n_minors (= the additional
        -- binders between params and field-Lams in rule-rhs).
        let field_doms_for_lams = list_lift_indices(field_doms, n_motives + n_minors, 0);
        let with_field_lams = wrap_lams(body, field_doms_for_lams);
        -- Wrap with minor Lams (innermost first, but our minor_doms is outermost first)
        let with_minor_lams = wrap_lams(with_field_lams, minor_doms);
        -- Wrap with N motive Lams (one per block member; multi-member mutual)
        let with_motive_lams = wrap_lams(with_minor_lams, motive_doms);
        -- Wrap with param Lams
        wrap_lams(with_motive_lams, param_doms),
    }
  }

  -- Recursor's univ params: [Param(0), ..., Param(total_lvls-1)].
  fn build_rec_lvls(total: G, i: G) -> List‹KLevel› {
    match total - i {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons(
          store(KLevelNode.Param(i)),
          build_rec_lvls(total, i + 1))),
    }
  }

  fn wrap_lams(body: KExpr, doms: List‹KExpr›) -> KExpr {
    match load(doms) {
      ListNode.Nil => body,
      ListNode.Cons(dom, rest) =>
        store(KExprNode.Lam(dom, wrap_lams(body, rest))),
    }
  }

  -- For each rec field j, append IH_j applied to `head`.
  -- IH_j = `Const(target_rec, rec_lvls) (params...) (motives...) (minors...) (idx_args) field_j`.
  -- target_rec = peer_recs[mem_idx] — the recursor for the field's own type.
  -- Mirror: src/ix/kernel/inductive.rs:3838-3956 fn build_rule_ih.
  -- Mirror src/ix/kernel/inductive.rs:3838-3956 fn build_rule_ih: WHNF the
  -- field's lifted dom and the inner body so the head/args reflect the
  -- true inductive occurrence (after reducing wrappers like
  -- `constType (n α) (n α)` → `n α`).
  fn apply_ihs(head: KExpr, rec_indices: List‹G›, rec_member_idxs: List‹G›,
               field_doms: List‹KExpr›,
               peer_recs: List‹G›, flat_own_params: List‹G›,
               n_params: G, n_motives: G, n_minors: G, n_fields: G,
               rec_lvls_list: List‹KLevel›, types: List‹KExpr›,
               top: List‹&KConstantInfo›, addrs: List‹Addr›, k: G) -> KExpr {
    match load(rec_indices) {
      ListNode.Nil => head,
      ListNode.Cons(field_idx, rest) =>
        let mem_idx = list_lookup(rec_member_idxs, k);
        let target_rec = list_lookup(peer_recs, mem_idx);
        let target_n_params = list_lookup(flat_own_params, mem_idx);
        let body_depth = n_params + n_motives + n_minors + n_fields;
        let dom = list_lookup(field_doms, field_idx);
        let dom_s1 = expr_lift(dom, n_fields - field_idx, 0);
        let dom_lifted = expr_lift(dom_s1, n_motives + n_minors, n_fields);
        let dom_w = whnf(dom_lifted, types, top, addrs);
        match peel_leading_foralls(dom_w) {
          (forall_doms, inner_body_raw) =>
            let inner_types = list_concat(list_reverse(forall_doms), types);
            let inner_body = whnf(inner_body_raw, inner_types, top, addrs);
            let n_xs = list_length(forall_doms);
            let inner_depth = body_depth + n_xs;
            let rec_const = store(KExprNode.Const(target_rec, rec_lvls_list));
            let with_params = build_apply_bvars_decreasing(rec_const, n_params, inner_depth - 1, 0);
            let with_motives = build_apply_motives(with_params, n_motives,
              ((inner_depth - 1) - n_params), 0);
            let with_minors = build_apply_minors(with_motives, n_minors,
              (((inner_depth - 1) - n_params) - n_motives), 0);
            match collect_spine(inner_body) {
              (_dh, dargs) =>
                let idx_args = list_drop(dargs, target_n_params);
                let with_idx = apply_spine(with_minors, idx_args);
                let field_base = ((n_fields - 1) - field_idx) + n_xs;
                let field_ref = store(KExprNode.BVar(field_base));
                let field_app = build_apply_xs(field_ref, n_xs, 0);
                let ih_inner = store(KExprNode.App(with_idx, field_app));
                let ih = wrap_lams(ih_inner, forall_doms);
                let new_head = store(KExprNode.App(head, ih));
                apply_ihs(new_head, rest, rec_member_idxs, field_doms, peer_recs,
                          flat_own_params, n_params, n_motives, n_minors, n_fields,
                          rec_lvls_list, types, top, addrs, k + 1),
            },
        },
    }
  }

  -- Apply n motives to `head`, each as BVar(start - i).
  fn build_apply_motives(head: KExpr, n_motives: G, start: G, i: G) -> KExpr {
    match n_motives - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - i));
        build_apply_motives(store(KExprNode.App(head, v)), n_motives, start, i + 1),
    }
  }

  fn build_apply_minors(head: KExpr, n_minors: G, start: G, i: G) -> KExpr {
    match n_minors - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - i));
        build_apply_minors(store(KExprNode.App(head, v)), n_minors, start, i + 1),
    }
  }

  -- Generate all KRecRules for an Indc's ctors via build_rule_rhs.
  -- Get the parent Indc's positional idx from a Recr's first rule.
  -- For solo recursors, all rules dispatch on ctors of the same Indc.
  -- Recursors with at least one rule: derive ind_idx via the rule's ctor.
  -- Recursors with NO rules (inductives with 0 ctors, e.g. False.rec /
  -- empty propositions): parse the recursor's type to extract the major's
  -- head Const(ind_idx). Mirrors `get_major_inductive_id` in Rust.
  fn rec_to_ind_idx_with_ty(rules: List‹KRecRule›, ty: KExpr,
                             n_params: G, n_motives: G, n_minors: G,
                             n_indices: G, top: List‹&KConstantInfo›) -> G {
    -- Derive ind_idx from the recursor's typ ONLY (walk past
    -- params+motives+minors+indices to reach `major`'s type, take its
    -- head Const). The rule-path was unreliable: rule.ctor_idx points
    -- to a Ctor whose own induct_idx was assigned at convert time using
    -- `find_matching_block_addr` heuristic — when multiple in-scope
    -- inductives share ctor count, that heuristic picks the wrong one.
    -- Mirror: src/ix/kernel/inductive.rs::rec_to_ind_idx (typ-only path).
    let skip = n_params + n_motives + n_minors + n_indices;
    let after_skip = peel_n_foralls(ty, skip);
    match load(after_skip) {
      KExprNode.Forall(major_ty, _) =>
        match collect_spine(major_ty) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(idx, _) => idx,
            },
        },
    }
  }

  -- Extract a declared recursor type's spec signature: the major-premise
  -- domain's leading `own` spine args, lowered from the major position
  -- to the recursor-param frame. For a non-aux recursor these are the
  -- recursor-param BVars themselves; for an aux recursor they equal the
  -- flat member's stored spec_params (both interned, so ptr comparison
  -- applies). Param args cannot reference index binders, so the lowering
  -- is capture-free for well-formed types.
  fn rec_declared_spec(ty: KExpr, n_p: G, n_mot: G, n_min: G, n_i: G,
                       own: G) -> List‹KExpr› {
    let pre_major = peel_n_foralls_tolerant(ty, ((n_p + n_mot) + n_min) + n_i);
    match load(pre_major) {
      KExprNode.Forall(major_dom, _) =>
        match collect_spine(major_dom) {
          (_head, args) =>
            let param_args = list_take(args, own);
            spec_params_lower(param_args, (n_mot + n_min) + n_i),
        },
      _ => store(ListNode.Nil),
    }
  }

  -- Find the Rec idx in `top` whose major inductive is `target_ind_idx`.
  -- Restricts to recursors with matching block_addr first (so aux Recs
  -- in the same block resolve before sibling-namespace Recs of the same
  -- external Indc), falling back to an unrestricted scan; returns 0
  -- (never a valid Rec) if not found. `want_spec_check = 0` matches any
  -- recursor whose major inductive is `target_ind_idx` (original
  -- members: idx is unambiguous). With 1, additionally require the
  -- declared spec signature to equal `target_sp` — aux recursors over
  -- the same external inductive (rec_1/rec_2) differ only in their
  -- spec_params.
  fn find_rec_for_ind(target_ind_idx: G, want_spec_check: G,
                      target_sp: List‹KExpr›, own: G, rec_block: Addr,
                      top: List‹&KConstantInfo›) -> G {
    let in_block = find_rec_for_ind_walk(target_ind_idx, want_spec_check,
                                         target_sp, own, rec_block, 1, top, top, 0);
    match in_block {
      0 => find_rec_for_ind_walk(target_ind_idx, want_spec_check,
                                 target_sp, own, rec_block, 0, top, top, 0),
      _ => in_block,
    }
  }

  fn find_rec_for_ind_walk(target_ind_idx: G, want_spec_check: G,
                           target_sp: List‹KExpr›, own: G, rec_block: Addr,
                           require_block: G,
                           consts: List‹&KConstantInfo›,
                           top: List‹&KConstantInfo›, idx: G) -> G {
    match load(consts) {
      ListNode.Nil => 0,
      ListNode.Cons(&ci, rest) =>
        match ci {
          KConstantInfo.Rec(_, ty, n_p, n_i, n_m, n_min, rules, _, _, ba) =>
            let rec_ind = rec_to_ind_idx_with_ty(rules, ty, n_p, n_m, n_min, n_i, top);
            let ind_match = eq_zero(rec_ind - target_ind_idx);
            let block_match = match require_block {
              0 => 1,
              _ => address_eq(ba, rec_block),
            };
            match ind_match * block_match {
              1 =>
                let spec_match = match want_spec_check {
                  0 => 1,
                  _ => spec_params_ptr_eq(
                         rec_declared_spec(ty, n_p, n_m, n_min, n_i, own),
                         target_sp),
                };
                match spec_match {
                  1 => idx,
                  0 => find_rec_for_ind_walk(target_ind_idx, want_spec_check,
                                             target_sp, own, rec_block,
                                             require_block, rest, top, idx + 1),
                },
              0 => find_rec_for_ind_walk(target_ind_idx, want_spec_check,
                                         target_sp, own, rec_block,
                                         require_block, rest, top, idx + 1),
            },
          _ => find_rec_for_ind_walk(target_ind_idx, want_spec_check,
                                     target_sp, own, rec_block,
                                     require_block, rest, top, idx + 1),
        },
    }
  }

  -- Build peer_recs[i] = rec_idx for flat[i], scoped to `rec_block`.
  -- Aux members select by (idx, spec signature) — idx alone aliases
  -- same-external-inductive auxes to the first peer recursor.
  fn build_peer_recs(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                     rec_block: Addr,
                     top: List‹&KConstantInfo›) -> List‹G› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (member_idx, is_aux, sp, _ou) =>
            let own = match load(list_lookup(top, member_idx)) {
              KConstantInfo.Induct(_, _, np, _, _, _, _) => np,
              _ => 0,
            };
            store(ListNode.Cons(
              find_rec_for_ind(member_idx, is_aux, sp, own, rec_block, top),
              build_peer_recs(rest, rec_block, top))),
        },
    }
  }

  fn rec_to_ind_idx(rules: List‹KRecRule›, top: List‹&KConstantInfo›) -> G {
    match load(rules) {
      ListNode.Cons(rule, _) =>
        match rule {
          KRecRule.Mk(ctor_idx, _, _) =>
            let ctor_ci = load(list_lookup(top, ctor_idx));
            match ctor_ci {
              KConstantInfo.Ctor(_, _, induct_idx, _, _, _, _) => induct_idx,
            },
        },
    }
  }

  -- Pairwise compare stored vs canonical KRecRule lists via k_is_def_eq.
  fn list_lift_indices(doms: List‹KExpr›, lift: G, i: G) -> List‹KExpr› {
    match load(doms) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(d, rest) =>
        let lifted = expr_lift(d, lift, i);
        store(ListNode.Cons(lifted, list_lift_indices(rest, lift, i + 1))),
    }
  }

  fn compare_rules(stored: List‹KRecRule›, canonical: List‹KRecRule›,
                   top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match load(stored) {
      ListNode.Nil =>
        match load(canonical) {
          ListNode.Nil => (),
        },
      ListNode.Cons(s, rs) =>
        match load(canonical) {
          ListNode.Cons(c, rc) =>
            match s {
              KRecRule.Mk(s_ctor, s_nf, s_rhs) =>
                match c {
                  KRecRule.Mk(c_ctor, c_nf, c_rhs) =>
                    assert_eq!(s_ctor, c_ctor);
                    assert_eq!(s_nf, c_nf);
                    let eq = k_is_def_eq(s_rhs, c_rhs, store(ListNode.Nil), top, addrs);
                    assert_eq!(eq, 1);
                    compare_rules(rs, rc, top, addrs),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- check_recursor_member (flat-aware: solo / mutual / nested-aux).
  --
  -- Mirror: src/ix/kernel/inductive.rs::check_recursor_member.
  -- For a stored Recr, regenerate canonical type + rules from the Indc
  -- and compare via k_is_def_eq. Resolves the canonical block via
  -- `resolve_primary_ind_for_rec` so aux recursors (e.g. Tree.rec_1) build
  -- their canonical form against the original block (Tree's), not the
  -- aux's external Indc block (List's).
  -- ============================================================================
  -- Mirror: src/ix/kernel/inductive.rs check_ctor_against_inductive_member.
  -- Validates that the Ctor's (induct_idx, cidx) cross-references the
  -- parent Indc's ctor_indices: `ctor_indices[cidx] == this_ctor_idx`.
  fn check_ctor_against_inductive_member(ctor_idx: G, ci_ctor: KConstantInfo,
                                          top: List‹&KConstantInfo›) {
    match ci_ctor {
      KConstantInfo.Ctor(_, _, induct_idx, cidx, _, _, _) =>
        let ind_ci = load(list_lookup(top, induct_idx));
        match ind_ci {
          KConstantInfo.Induct(_, _, _, _, ctor_indices, _, _) =>
            let expected = list_lookup(ctor_indices, cidx);
            assert_eq!(expected, ctor_idx);
            (),
        },
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:4451-4489 compute_k_target.
  -- K-target valid iff: solo block, result level == 0 (Prop), single ctor
  -- with zero non-param fields. Returns 1 if K-target, else 0.
  fn compute_k_target(ind_idx: G, top: List‹&KConstantInfo›) -> G {
    let ind_ci = load(list_lookup(top, ind_idx));
    match ind_ci {
      KConstantInfo.Induct(_, ind_ty, n_params, n_indices, ctor_indices, _, _) =>
        let block_members = derive_block_member_idxs(ind_idx, top);
        match list_length(block_members) - 1 {
          0 =>
            let result_level = get_result_sort_level(ind_ty, n_params + n_indices);
            match level_equal(result_level, store(KLevelNode.Zero)) {
              0 => 0,
              1 =>
                match list_length(ctor_indices) - 1 {
                  0 =>
                    let ctor_idx = list_lookup(ctor_indices, 0);
                    let ctor_ci = load(list_lookup(top, ctor_idx));
                    match ctor_ci {
                      KConstantInfo.Ctor(_, _, _, _, _, n_fields, _) => eq_zero(n_fields),
                      _ => 0,
                    },
                  _ => 0,
                },
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Structural KExpr equality (heads + payload only; ignores universes/binder
  -- names). Used to compare a ctor field's spine-arg prefix against a flat
  -- aux member's spec_params in `is_rec_field`, where content-addressed exprs
  -- from the same block-flattening pass are guaranteed to be structurally
  -- comparable without WHNF.
  fn kexpr_struct_eq(a: KExpr, b: KExpr) -> G {
    match load(a) {
      KExprNode.BVar(ia) =>
        match load(b) {
          KExprNode.BVar(ib) =>
            match (u32_less_than(ia, ib) + u32_less_than(ib, ia)) {
              0 => 1,
              _ => 0,
            },
          _ => 0,
        },
      KExprNode.Srt(_) =>
        match load(b) {
          KExprNode.Srt(_) => 1,
          _ => 0,
        },
      KExprNode.Const(ca, _) =>
        match load(b) {
          KExprNode.Const(cb, _) =>
            match (u32_less_than(ca, cb) + u32_less_than(cb, ca)) {
              0 => 1,
              _ => 0,
            },
          _ => 0,
        },
      KExprNode.App(fa, aa) =>
        match load(b) {
          KExprNode.App(fb, ab) =>
            let feq = kexpr_struct_eq(fa, fb);
            match feq {
              1 => kexpr_struct_eq(aa, ab),
              _ => 0,
            },
          _ => 0,
        },
      KExprNode.Lam(ta, ba) =>
        match load(b) {
          KExprNode.Lam(tb, bb) =>
            let teq = kexpr_struct_eq(ta, tb);
            match teq {
              1 => kexpr_struct_eq(ba, bb),
              _ => 0,
            },
          _ => 0,
        },
      KExprNode.Forall(da, xa) =>
        match load(b) {
          KExprNode.Forall(db, xb) =>
            let deq = kexpr_struct_eq(da, db);
            match deq {
              1 => kexpr_struct_eq(xa, xb),
              _ => 0,
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Resolve the declared recursor's flat-member POSITION. Aux recursors
  -- over the same external inductive (rec_1/rec_2 with different
  -- spec_params) share self_major's const idx, so an idx lookup aliases
  -- them all to the first entry; disambiguate by the declared type's
  -- major-premise domain: its spine's param args, lowered to the
  -- recursor-param frame, must equal the flat member's stored
  -- spec_params. Falls back to the first idx match (originals match on
  -- idx alone — their spec_params are empty). A malformed declared type
  -- only mis-selects a candidate; the declared-vs-canonical assert
  -- still rejects. Mirror: the signature-based match in Rust
  -- check_recursor_member (inductive.rs:4181-4219).
  fn find_rec_self_pos(ty: KExpr, n_p: G, n_mot: G, n_min: G, n_i: G,
                       self_major: G,
                       flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                       top: List‹&KConstantInfo›) -> G {
    let self_ci = load(list_lookup(top, self_major));
    match self_ci {
      KConstantInfo.Induct(_, _, own, _, _, _, _) =>
        let lowered = rec_declared_spec(ty, n_p, n_mot, n_min, n_i, own);
        find_rec_self_pos_walk(flat, self_major, lowered, 0, 0),
      _ => 0,
    }
  }

  -- `first_any` = 1 + position of the first idx match seen (0 = none):
  -- the fallback when no spec_params signature matches.
  fn find_rec_self_pos_walk(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                            target_idx: G, largs: List‹KExpr›,
                            i: G, first_any: G) -> G {
    match load(flat) {
      ListNode.Nil =>
        match first_any {
          0 => 0,
          _ => first_any - 1,
        },
      ListNode.Cons(m, rest) =>
        match m {
          (fidx, is_aux, sp, _ou) =>
            match (u32_less_than(fidx, target_idx) + u32_less_than(target_idx, fidx)) {
              0 =>
                let new_first = match first_any { 0 => i + 1, _ => first_any, };
                match is_aux {
                  0 => i,
                  _ =>
                    match spec_params_ptr_eq(sp, largs) {
                      1 => i,
                      0 => find_rec_self_pos_walk(rest, target_idx, largs,
                                                  i + 1, new_first),
                    },
                },
              _ => find_rec_self_pos_walk(rest, target_idx, largs, i + 1, first_any),
            },
        },
    }
  }

  fn check_recursor_member(rec_idx: G, ci_rec: KConstantInfo,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match ci_rec {
      KConstantInfo.Rec(_, ty, n_p, n_i, n_mot, n_min, rules, k_flag, _, rec_block) =>
        -- For aux recursors (Tree.rec_1 etc), the "primary" inductive is the
        -- one whose block carries the auxes — discoverable in the same rec_block.
        -- Use it as the canonical-block source. Self's major may be different
        -- (an external aux ind).
        let self_major = rec_to_ind_idx_with_ty(rules, ty, n_p, n_mot, n_min, n_i, top);
        let ind_idx = resolve_primary_ind_for_rec(self_major, rec_block, top);
        let computed_k = compute_k_target(self_major, top);
        assert_eq!(k_flag, computed_k);
        let primary_ci = load(list_lookup(top, ind_idx));
        let self_ci = load(list_lookup(top, self_major));
        match primary_ci {
          KConstantInfo.Induct(ind_lvls, ind_ty, ind_n_params, _, _, _, _) =>
            match self_ci {
              KConstantInfo.Induct(_, self_ind_ty, self_own_params, self_n_indices, self_ctor_indices, _, _) =>
                -- Re-derive elim_level / univ_offset using self's data.
                let result_level = get_result_sort_level(self_ind_ty, self_own_params + self_n_indices);
                let univ_offset = is_large_eliminator(result_level, self_ctor_indices, top, addrs);
                let elim_level = match univ_offset {
                  1 => store(KLevelNode.Param(0)),
                  0 => store(KLevelNode.Zero),
                };
                let block_member_idxs = derive_block_member_idxs(ind_idx, top);
                let flat = build_flat_block(block_member_idxs, univ_offset, top);
                let self_pos = find_rec_self_pos(ty, n_p, n_mot, n_min, n_i,
                                                 self_major, flat, top);
                let canonical_ty = build_rec_type(self_major, self_ind_ty, self_ctor_indices,
                                                   ind_n_params, self_n_indices, ind_lvls,
                                                   self_own_params, ind_idx, self_pos,
                                                   top, addrs);
                let ty_eq = k_is_def_eq(ty, canonical_ty, store(ListNode.Nil), top, addrs);
                assert_eq!(ty_eq, 1);
                let flat_idxs = flat_ind_idxs(flat);
                let n_motives = list_length(flat);
                let n_rec_params = ind_n_params;
                let motive_base = n_rec_params;
                let flat_own_params = flat_own_params_of(flat, top);
                let motive_doms = build_all_motives(flat, ind_n_params,
                                                    ind_lvls, elim_level, univ_offset,
                                                    n_rec_params, top);
                let minor_doms = build_all_minors(flat, flat_idxs, flat_own_params,
                                                   n_rec_params, n_motives,
                                                   ind_lvls, univ_offset, motive_base, top, addrs, 0);
                let n_minors = list_length(minor_doms);
                -- Rules cover SELF's ctors only. ctor_pos_offset = sum of
                -- |ctors| for flat members preceding self in flat order.
                -- Count by POSITION (self_pos), not by idx: same-idx aux
                -- members would stop the walk at the first occurrence.
                let ctor_pos_offset = ctors_before_pos(flat_idxs, self_pos, top, 0);
                let occ_us = build_param_lvls_range(univ_offset, ind_lvls, 0);
                let ind_ty_inst = expr_inst_levels(ind_ty, occ_us);
                let params_walk = collect_n_doms(ind_ty_inst, ind_n_params);
                match params_walk {
                  (param_doms, _) =>
                    let peer_recs = build_peer_recs(flat, rec_block, top);
                    -- Self's flat member by signature-resolved position
                    -- (idx lookup would alias same-idx aux recursors).
                    let self_member = flat_member_at(flat, self_pos);
                    let self_is_aux = match self_member { (_, ia, _, _) => ia, };
                    let self_spec_params = match self_member { (_, _, sp, _) => sp, };
                    let self_occ_us = match self_member { (_, _, _, ou) => ou, };
                    let canonical_rules = populate_rules(rec_idx, self_major, self_ctor_indices,
                                                         ind_n_params, n_motives, n_minors,
                                                         ind_lvls, univ_offset,
                                                         motive_doms, minor_doms, param_doms,
                                                         peer_recs, flat, flat_idxs, flat_own_params,
                                                         self_is_aux, self_spec_params, self_occ_us,
                                                         top, addrs, ctor_pos_offset);
                    compare_rules(rules, canonical_rules, top, addrs),
                },
            },
        },
    }
  }

  -- Build flat block members: [originals from block_member_idxs] ++
  -- [auxes from gather_block_nested]. Each entry is (ind_idx, is_aux,
  -- spec_params, occurrence_us). For originals: is_aux=0, spec_params=[],
  -- occurrence_us = build_param_lvls_range(univ_offset, lvls, 0). For
  -- auxes: is_aux=1, ind_idx=ext_ind_idx, spec_params=detected substitution
  -- exprs, occurrence_us = univ args from the actual nested ref.
  -- Mirror: src/ix/kernel/inductive.rs:490-601 build_flat_block.
  -- Queue-based fixed-point build. Mirror `crates/kernel/src/inductive.rs`
  -- `build_flat_block:531-599`. Seed with originals, then iteratively scan
  -- every discovered member's ctors for further nested occurrences; every
  -- newly-detected aux gets pushed onto the flat list AND its own ctors
  -- scanned in the next round.
  fn build_flat_block(block_member_idxs: List‹G›, univ_offset: G,
                      top: List‹&KConstantInfo›)
                      -> List‹(G, G, List‹KExpr›, List‹KLevel›)› {
    let originals = build_flat_originals(block_member_idxs, univ_offset, top);
    build_flat_block_iter(originals, 0, block_member_idxs, top)
  }

  fn build_flat_block_iter(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                           qi: G, block_member_idxs: List‹G›,
                           top: List‹&KConstantInfo›)
                           -> List‹(G, G, List‹KExpr›, List‹KLevel›)› {
    let n = list_length(flat);
    let more = u32_less_than(qi, n);
    match more {
      0 => flat,
      _ =>
        let member = flat_member_at(flat, qi);
        match member {
          (m_idx, is_aux, sp, ou) =>
            let new_triples = detect_nested_in_member(m_idx, is_aux, sp, ou,
                                                       block_member_idxs, top);
            let flat_updated = flat_append_new_auxes(flat, new_triples);
            build_flat_block_iter(flat_updated, qi + 1, block_member_idxs, top),
        },
    }
  }

  fn detect_nested_in_member(m_idx: G, is_aux: G,
                             spec_params: List‹KExpr›,
                             occ_us: List‹KLevel›,
                             block_idxs: List‹G›,
                             top: List‹&KConstantInfo›)
                             -> List‹(G, List‹KExpr›, List‹KLevel›)› {
    let ci = load(list_lookup(top, m_idx));
    match ci {
      KConstantInfo.Induct(_, _, n_params, _, ctor_indices, _, _) =>
        detect_nested_in_member_ctors(ctor_indices, n_params, is_aux,
                                       spec_params, occ_us, block_idxs, top),
      _ => store(ListNode.Nil),
    }
  }

  fn detect_nested_in_member_ctors(ctor_indices: List‹G›, n_params: G,
                                    is_aux: G, spec_params: List‹KExpr›,
                                    occ_us: List‹KLevel›,
                                    block_idxs: List‹G›,
                                    top: List‹&KConstantInfo›)
                                    -> List‹(G, List‹KExpr›, List‹KLevel›)› {
    match load(ctor_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(ctor_idx, rest) =>
        let ctor_ci = load(list_lookup(top, ctor_idx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _) =>
            let body = match is_aux {
              0 => peel_n_foralls_tolerant(ctor_ty, n_params),
              _ =>
                let ctor_ty_inst = expr_inst_levels(ctor_ty, occ_us);
                synth_aux_ctor_ty(ctor_ty_inst, n_params, spec_params),
            };
            let from_this = detect_nested_in_field_chain(body, block_idxs, top, 0);
            let from_rest = detect_nested_in_member_ctors(rest, n_params, is_aux,
                                                          spec_params, occ_us,
                                                          block_idxs, top);
            list_concat(from_this, from_rest),
          _ => detect_nested_in_member_ctors(rest, n_params, is_aux,
                                              spec_params, occ_us, block_idxs, top),
        },
    }
  }

  fn flat_append_new_auxes(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                           new_triples: List‹(G, List‹KExpr›, List‹KLevel›)›)
                           -> List‹(G, G, List‹KExpr›, List‹KLevel›)› {
    match load(new_triples) {
      ListNode.Nil => flat,
      ListNode.Cons(t, rest) =>
        match t {
          (idx, sp, ou) =>
            match flat_contains_aux(flat, idx, sp) {
              1 => flat_append_new_auxes(flat, rest),
              _ =>
                let singleton = store(ListNode.Cons((idx, 1, sp, ou),
                                                     store(ListNode.Nil)));
                let flat_appended = list_concat(flat, singleton);
                flat_append_new_auxes(flat_appended, rest),
            },
        },
    }
  }

  -- Dedup key = (ext ind idx, spec_params). Two auxes on the same
  -- external inductive with different spec_params are distinct flat
  -- members (Rust: aux_seen keyed on (addr, spec param hashes),
  -- inductive.rs:732-743). A non-aux entry matches on idx alone —
  -- block originals are never re-added as auxes (Rust: the !is_aux
  -- flat skip at inductive.rs:672). spec_params are compared
  -- element-wise by ptr_val: both sides are stored in the de-lifted
  -- recursor-param frame, and the executor interns stores by content,
  -- so equal content means equal ptr in honest traces; a de-interned
  -- malicious witness can only cause a dedup MISS (extra aux → flat
  -- count mismatch → reject), never a false collapse.
  fn flat_contains_aux(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                       target_idx: G, target_sp: List‹KExpr›) -> G {
    match load(flat) {
      ListNode.Nil => 0,
      ListNode.Cons(m, rest) =>
        match m {
          (idx, is_aux, sp, _ou) =>
            match (u32_less_than(idx, target_idx) + u32_less_than(target_idx, idx)) {
              0 =>
                match is_aux {
                  0 => 1,
                  _ =>
                    match spec_params_ptr_eq(sp, target_sp) {
                      1 => 1,
                      0 => flat_contains_aux(rest, target_idx, target_sp),
                    },
                },
              _ => flat_contains_aux(rest, target_idx, target_sp),
            },
        },
    }
  }

  fn spec_params_ptr_eq(a: List‹KExpr›, b: List‹KExpr›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          ListNode.Cons(_, _) => 0,
        },
      ListNode.Cons(x, xs) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(y, ys) =>
            match ptr_val(x) - ptr_val(y) {
              0 => spec_params_ptr_eq(xs, ys),
              _ => 0,
            },
        },
    }
  }

  fn build_flat_originals(block_member_idxs: List‹G›, univ_offset: G,
                          top: List‹&KConstantInfo›)
                          -> List‹(G, G, List‹KExpr›, List‹KLevel›)› {
    match load(block_member_idxs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(idx, rest) =>
        let ci = load(list_lookup(top, idx));
        match ci {
          KConstantInfo.Induct(lvls, _, _, _, _, _, _) =>
            let occ_us = build_param_lvls_range(univ_offset, lvls, 0);
            store(ListNode.Cons((idx, 0, store(ListNode.Nil), occ_us),
              build_flat_originals(rest, univ_offset, top))),
          _ =>
            store(ListNode.Cons((idx, 0, store(ListNode.Nil), store(ListNode.Nil)),
              build_flat_originals(rest, univ_offset, top))),
        },
    }
  }

  -- Project per-member ind_idx from flat list.
  fn flat_ind_idxs(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›) -> List‹G› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (ind_idx, _, _, _) =>
            store(ListNode.Cons(ind_idx, flat_ind_idxs(rest))),
        },
    }
  }

  -- Look up nth flat member.
  fn flat_member_at(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›, n: G)
                    -> (G, G, List‹KExpr›, List‹KLevel›) {
    match load(flat) {
      ListNode.Nil => (0, 0, store(ListNode.Nil), store(ListNode.Nil)),
      ListNode.Cons(m, rest) =>
        match n {
          0 => m,
          _ => flat_member_at(rest, n - 1),
        },
    }
  }

  -- Build major args. Non-aux: apply n_rec_params recursor-param BVars at
  -- decreasing positions starting from `start`. Aux: apply each spec_param
  -- lifted by `spec_lift` — the binders between the recursor-param frame
  -- and the major position (n_motives + n_minors + n_indices in the
  -- recursor type).
  fn build_major_args_for_self(head: KExpr, n_rec_params: G, start: G,
                                spec_lift: G,
                                is_aux: G, spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => build_apply_bvars_decreasing(head, n_rec_params, start, 0),
      _ => apply_spec_params_lifted(head, spec_params, spec_lift),
    }
  }

  -- For each flat member, look up its own_params from top.
  fn flat_own_params_of(flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                       top: List‹&KConstantInfo›) -> List‹G› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (ind_idx, _, _, _) =>
            let ci = load(list_lookup(top, ind_idx));
            match ci {
              KConstantInfo.Induct(_, _, np, _, _, _, _) =>
                store(ListNode.Cons(np, flat_own_params_of(rest, top))),
              _ =>
                store(ListNode.Cons(0, flat_own_params_of(rest, top))),
            },
        },
    }
  }

  -- Find the primary inductive for the canonical block of a recursor.
  -- Walk recs in `rec_block`; pick the first one whose major's `nested > 0`
  -- (= the original Indc whose ctors carry nested occurrences). Returns
  -- (found, ind_idx); on `found = 0` callers fall back to `self_major`.
  fn resolve_primary_ind_for_rec(self_major: G, rec_block: Addr,
                                  top: List‹&KConstantInfo›) -> G {
    match address_eq(rec_block, store([0u8; 32])) {
      1 => self_major,
      0 =>
        let p = scan_primary_in_rec_block(rec_block, top, top, 0);
        match p {
          (1, idx) => idx,
          _ => self_major,
        },
    }
  }

  -- Returns 1 iff `idx`'s own ctor fields contain a nested occurrence
  -- (external inductive applied to args mentioning block members).
  -- Structural replacement for the dropped Ixon `nested` count: an
  -- original of a nested-emitting block detects non-empty; an aux (whose
  -- specialized ctors reference only block members) and a pure-mutual
  -- peer detect empty. Aiur memoization caches per (idx, block, top).
  fn member_has_nested(idx: G, block_idxs: List‹G›,
                       top: List‹&KConstantInfo›) -> G {
    let nested = detect_nested_in_orig(idx, block_idxs, top);
    match load(nested) {
      ListNode.Nil => 0,
      _ => 1,
    }
  }

  fn any_member_has_nested(walk_idxs: List‹G›, block_idxs: List‹G›,
                           top: List‹&KConstantInfo›) -> G {
    match load(walk_idxs) {
      ListNode.Nil => 0,
      ListNode.Cons(idx, rest) =>
        match member_has_nested(idx, block_idxs, top) {
          1 => 1,
          0 => any_member_has_nested(rest, block_idxs, top),
        },
    }
  }

  -- Returns 1 iff `ind_idx`'s block emits nested auxes.
  fn ind_has_nested(ind_idx: G, top: List‹&KConstantInfo›) -> G {
    let block_idxs = derive_block_member_idxs(ind_idx, top);
    any_member_has_nested(block_idxs, block_idxs, top)
  }

  fn scan_primary_in_rec_block(rec_block: Addr,
                               consts: List‹&KConstantInfo›,
                               top: List‹&KConstantInfo›, idx: G) -> (G, G) {
    match load(consts) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(&ci, rest) =>
        match ci {
          KConstantInfo.Rec(_, ty, n_p, n_i, n_m, n_min, rules, _, _, ba) =>
            match address_eq(ba, rec_block) {
              0 => scan_primary_in_rec_block(rec_block, rest, top, idx + 1),
              1 =>
                let r_ind = rec_to_ind_idx_with_ty(rules, ty, n_p, n_m, n_min, n_i, top);
                let r_ci = load(list_lookup(top, r_ind));
                match r_ci {
                  KConstantInfo.Induct(_, _, _, _, _, _, _) =>
                    match ind_has_nested(r_ind, top) {
                      0 => scan_primary_in_rec_block(rec_block, rest, top, idx + 1),
                      _ => (1, r_ind),
                    },
                  _ => scan_primary_in_rec_block(rec_block, rest, top, idx + 1),
                },
            },
          _ => scan_primary_in_rec_block(rec_block, rest, top, idx + 1),
        },
    }
  }

  -- Sum of |ctors| over the first `target_pos` block members.
  fn ctors_before_pos(block_member_idxs: List‹G›, target_pos: G,
                      top: List‹&KConstantInfo›, acc: G) -> G {
    match target_pos {
      0 => acc,
      _ =>
        match load(block_member_idxs) {
          ListNode.Nil => acc,
          ListNode.Cons(member_idx, rest) =>
            let ci = load(list_lookup(top, member_idx));
            match ci {
              KConstantInfo.Induct(_, _, _, _, m_ctors, _, _) =>
                ctors_before_pos(rest, target_pos - 1, top,
                                 acc + list_length(m_ctors)),
              _ => ctors_before_pos(rest, target_pos - 1, top, acc),
            },
        },
    }
  }

  -- Returns 1 iff `ci_idx` is an auxiliary Inductive in its block.
  -- Aux iff: in a non-solo block AND own ctors contain no nested
  -- occurrence AND some block member's do (i.e., the block is a
  -- nested-emitting block, not pure mutual). Structural — the Ixon
  -- `nested` count this used to read was dropped.
  fn is_aux_inductive(ci_idx: G, top: List‹&KConstantInfo›) -> G {
    let ci = load(list_lookup(top, ci_idx));
    match ci {
      KConstantInfo.Induct(_, _, _, _, _, _, this_block_addr) =>
        match address_eq(this_block_addr, store([0u8; 32])) {
          1 => 0,
          0 =>
            let block_idxs = derive_block_member_idxs(ci_idx, top);
            match member_has_nested(ci_idx, block_idxs, top) {
              0 => any_member_has_nested(block_idxs, block_idxs, top),
              _ => 0,
            },
        },
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:619+
  -- fn try_detect_nested. For each ctor of `orig_idx`, walk its fields;
  -- for each field's domain, peel leading Foralls + check spine head:
  -- if head is non-block Inductive AND first ext_n_params args mention
  -- block_idxs, record (ext_idx, spec_params).
  fn detect_nested_in_orig(orig_idx: G, block_idxs: List‹G›,
                           top: List‹&KConstantInfo›)
                           -> List‹(G, List‹KExpr›, List‹KLevel›)› {
    let orig_ci = load(list_lookup(top, orig_idx));
    match orig_ci {
      KConstantInfo.Induct(_, _, n_params, _, ctor_indices, _, _) =>
        detect_nested_in_ctors(ctor_indices, n_params, block_idxs, top),
      _ => store(ListNode.Nil),
    }
  }

  fn detect_nested_in_ctors(ctor_indices: List‹G›, n_params: G,
                            block_idxs: List‹G›,
                            top: List‹&KConstantInfo›)
                            -> List‹(G, List‹KExpr›, List‹KLevel›)› {
    match load(ctor_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(ctor_idx, rest) =>
        let ctor_ci = load(list_lookup(top, ctor_idx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _) =>
            let body = peel_n_foralls_tolerant(ctor_ty, n_params);
            let from_this = detect_nested_in_field_chain(body, block_idxs, top, 0);
            let from_rest = detect_nested_in_ctors(rest, n_params, block_idxs, top);
            list_concat(from_this, from_rest),
          _ => detect_nested_in_ctors(rest, n_params, block_idxs, top),
        },
    }
  }

  -- `depth` = number of binders between the constructor's param context
  -- and the current position (field binders walked so far, plus leading
  -- foralls peeled off the domain in `detect_nested_in_dom`). Both call
  -- paths (originals after `peel_n_foralls_tolerant`, auxes after
  -- `synth_aux_ctor_ty` substitution) start at 0.
  fn detect_nested_in_field_chain(ty: KExpr, block_idxs: List‹G›,
                                   top: List‹&KConstantInfo›, depth: G)
                                   -> List‹(G, List‹KExpr›, List‹KLevel›)› {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let from_dom = detect_nested_in_dom(dom, block_idxs, top, depth);
        let from_rest = detect_nested_in_field_chain(body, block_idxs, top,
                                                     depth + 1);
        list_concat(from_dom, from_rest),
      _ => store(ListNode.Nil),
    }
  }

  fn detect_nested_in_dom(dom: KExpr, block_idxs: List‹G›,
                          top: List‹&KConstantInfo›, depth: G)
                          -> List‹(G, List‹KExpr›, List‹KLevel›)› {
    match peel_leading_foralls(dom) {
      (doms, body) =>
        match collect_spine(body) {
          (head, args) =>
            match load(head) {
              KExprNode.Const(idx, occ_us) =>
                match list_contains_g(block_idxs, idx) {
                  1 => store(ListNode.Nil),
                  0 =>
                    let ci = load(list_lookup(top, idx));
                    match ci {
                      KConstantInfo.Induct(_, _, ext_n_params, _, _, _, _) =>
                        let n_args = list_length(args);
                        match u32_less_than(n_args, ext_n_params) {
                          1 => store(ListNode.Nil),
                          0 =>
                            let param_args = list_take(args, ext_n_params);
                            match list_any_mentions(param_args, block_idxs) {
                              0 => store(ListNode.Nil),
                              1 =>
                                -- S7: reject occurrences whose param args
                                -- reference a field/domain-local binder — a
                                -- loose BVar below the extraction depth. Not
                                -- a valid nested-inductive parameterization;
                                -- no aux may be synthesized. Mirror:
                                -- crates/kernel/src/inductive.rs:723-730
                                -- (`sp.has_fvars()` — Rust opens those
                                -- binders as fvars, Aiur keeps de Bruijn).
                                let d = depth + list_length(doms);
                                match spec_params_valid(param_args, d) {
                                  0 => store(ListNode.Nil),
                                  1 =>
                                    -- De-lift to the recursor-param frame
                                    -- (block param j at BVar(n_params-1-j)):
                                    -- the storage convention every flat
                                    -- consumer assumes, and the frame that
                                    -- makes the same occurrence at two
                                    -- field depths compare equal for aux
                                    -- dedup. Sound: S7 above guarantees no
                                    -- loose BVar below `d`.
                                    let lowered = spec_params_lower(param_args, d);
                                    store(ListNode.Cons((idx, lowered, occ_us),
                                                         store(ListNode.Nil))),
                                },
                            },
                        },
                      _ => store(ListNode.Nil),
                    },
                },
              _ => store(ListNode.Nil),
            },
        },
    }
  }

  -- 1 iff no spec_param references a binder below extraction depth `d`.
  fn spec_params_valid(sps: List‹KExpr›, d: G) -> G {
    match load(sps) {
      ListNode.Nil => 1,
      ListNode.Cons(sp, rest) =>
        match has_bvar_in_range(sp, 0, d) {
          1 => 0,
          0 => spec_params_valid(rest, d),
        },
    }
  }

  fn spec_params_lower(sps: List‹KExpr›, d: G) -> List‹KExpr› {
    match load(sps) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(sp, rest) =>
        store(ListNode.Cons(expr_lower(sp, d, 0), spec_params_lower(rest, d))),
    }
  }

  -- Synthesize canonical aux.ind_ty from
  -- ext's ind_ty + spec_params. Mirror: src/ix/kernel/inductive.rs
  -- canonical_aux_order's synthetic indc construction.
  -- Mechanism: peel ext's first ext_n_params Pi binders, substituting each
  -- with the corresponding spec_param. Result is the body (indices + sort)
  -- with α-substitution applied — ext's signature specialized at spec_params.
  fn synth_aux_ind_ty(ext_ind_ty: KExpr, ext_n_params: G,
                      spec_params: List‹KExpr›) -> KExpr {
    synth_aux_subst(ext_ind_ty, ext_n_params, spec_params, 0)
  }

  -- Walk first n Pi binders. For each, substitute the binder's BVar(0) with
  -- spec_params[k] (lifted appropriately).
  fn synth_aux_subst(ty: KExpr, n: G, spec_params: List‹KExpr›, k: G) -> KExpr {
    match n {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            let sp = list_lookup(spec_params, k);
            let body_substed = expr_inst1(body, sp, 0);
            synth_aux_subst(body_substed, n - 1, spec_params, k + 1),
        },
    }
  }

  -- Synthesize canonical aux.ctor_ty from ext.ctor_ty + spec_params.
  -- Same substitution but applied to a ctor type (which has ext's params
  -- as leading Pi binders too).
  fn synth_aux_ctor_ty(ext_ctor_ty: KExpr, ext_n_params: G,
                       spec_params: List‹KExpr›) -> KExpr {
    synth_aux_subst(ext_ctor_ty, ext_n_params, spec_params, 0)
  }

  -- Mirror: src/ix/kernel/inductive.rs
  -- canonical_aux_order. For each aux in `block_idxs`, find a matching
  -- nested occurrence in some non-aux original's ctors and verify aux's
  -- ind_ty matches the synthesized canonical (ext.ind_ty with spec_params
  -- substituted).
  fn validate_block_auxes(block_idxs: List‹G›, top: List‹&KConstantInfo›) {
    let nested_list = gather_block_nested(block_idxs, block_idxs, top);
    -- Block_param_decls = first n_params Pi domains of first non-aux original.
    let bp_pair = block_param_decls(block_idxs, top);
    match bp_pair {
      (n_block_params, block_param_doms) =>
        validate_auxes_walk(block_idxs, nested_list, n_block_params,
                            block_param_doms, top),
    }
  }

  -- Find first non-aux original; return (n_params, first n_params Pi domains).
  fn block_param_decls(walk_idxs: List‹G›,
                       top: List‹&KConstantInfo›) -> (G, List‹KExpr›) {
    match load(walk_idxs) {
      ListNode.Nil => (0, store(ListNode.Nil)),
      ListNode.Cons(idx, rest) =>
        match is_aux_inductive(idx, top) {
          1 => block_param_decls(rest, top),
          0 =>
            let ci = load(list_lookup(top, idx));
            match ci {
              KConstantInfo.Induct(_, ind_ty, n_params, _, _, _, _) =>
                let walk = collect_n_doms(ind_ty, n_params);
                match walk {
                  (doms, _) => (n_params, doms),
                },
              _ => block_param_decls(rest, top),
            },
        },
    }
  }

  -- Collect detected nested occurrences across all non-aux originals in block.
  fn gather_block_nested(walk_idxs: List‹G›, all_block_idxs: List‹G›,
                         top: List‹&KConstantInfo›)
                         -> List‹(G, List‹KExpr›, List‹KLevel›)› {
    match load(walk_idxs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(idx, rest) =>
        match is_aux_inductive(idx, top) {
          1 => gather_block_nested(rest, all_block_idxs, top),
          0 =>
            let from_orig = detect_nested_in_orig(idx, all_block_idxs, top);
            let from_rest = gather_block_nested(rest, all_block_idxs, top);
            list_concat(from_orig, from_rest),
        },
    }
  }

  -- Walk auxes in block; for each, assert it matches some nested occurrence.
  fn validate_auxes_walk(walk_idxs: List‹G›,
                         nested_list: List‹(G, List‹KExpr›, List‹KLevel›)›,
                         n_block_params: G,
                         block_param_doms: List‹KExpr›,
                         top: List‹&KConstantInfo›) {
    match load(walk_idxs) {
      ListNode.Nil => (),
      ListNode.Cons(idx, rest) =>
        match is_aux_inductive(idx, top) {
          0 => validate_auxes_walk(rest, nested_list, n_block_params, block_param_doms, top),
          1 =>
            let aux_ci = load(list_lookup(top, idx));
            match aux_ci {
              KConstantInfo.Induct(_, aux_ind_ty, _, _, aux_ctor_indices, _, _) =>
                let matched = try_match_aux(aux_ind_ty, aux_ctor_indices, nested_list,
                                             n_block_params, block_param_doms, top);
                assert_eq!(matched, 1);
                validate_auxes_walk(rest, nested_list, n_block_params, block_param_doms, top),
              _ => validate_auxes_walk(rest, nested_list, n_block_params, block_param_doms, top),
            },
        },
    }
  }

  -- Returns 1 iff aux's ind_ty matches (block_params Pi → ext.ind_ty[α := spec_params])
  -- AND ctor count matches AND each ctor ty matches likewise.
  fn try_match_aux(aux_ind_ty: KExpr, aux_ctor_indices: List‹G›,
                   nested_list: List‹(G, List‹KExpr›, List‹KLevel›)›,
                   n_block_params: G,
                   block_param_doms: List‹KExpr›,
                   top: List‹&KConstantInfo›) -> G {
    match load(nested_list) {
      ListNode.Nil => 0,
      ListNode.Cons(occ, rest) =>
        match occ {
          (ext_idx, spec_params, _occ_us) =>
            let ext_ci = load(list_lookup(top, ext_idx));
            match ext_ci {
              KConstantInfo.Induct(_, ext_ind_ty, ext_n_params, _, ext_ctor_indices, _, _) =>
                let body = synth_aux_ind_ty(ext_ind_ty, ext_n_params, spec_params);
                let synth = wrap_foralls(body, block_param_doms);
                let cmp = compare_kexpr(synth, aux_ind_ty);
                match cmp {
                  1 =>
                    let aux_n = list_length(aux_ctor_indices);
                    let ext_n = list_length(ext_ctor_indices);
                    match aux_n - ext_n {
                      0 =>
                        let ctors_ok = compare_aux_ctors(aux_ctor_indices, ext_ctor_indices,
                                                          ext_n_params, spec_params,
                                                          block_param_doms, top);
                        match ctors_ok {
                          1 => 1,
                          _ => try_match_aux(aux_ind_ty, aux_ctor_indices, rest,
                                              n_block_params, block_param_doms, top),
                        },
                      _ => try_match_aux(aux_ind_ty, aux_ctor_indices, rest,
                                          n_block_params, block_param_doms, top),
                    },
                  _ => try_match_aux(aux_ind_ty, aux_ctor_indices, rest,
                                      n_block_params, block_param_doms, top),
                },
              _ => try_match_aux(aux_ind_ty, aux_ctor_indices, rest,
                                  n_block_params, block_param_doms, top),
            },
        },
    }
  }

  -- Pairwise compare aux ctors against ext ctors with spec_params substituted.
  fn compare_aux_ctors(aux_ctor_indices: List‹G›, ext_ctor_indices: List‹G›,
                       ext_n_params: G, spec_params: List‹KExpr›,
                       block_param_doms: List‹KExpr›,
                       top: List‹&KConstantInfo›) -> G {
    match load(aux_ctor_indices) {
      ListNode.Nil =>
        match load(ext_ctor_indices) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(aux_c_idx, aux_rest) =>
        match load(ext_ctor_indices) {
          ListNode.Nil => 0,
          ListNode.Cons(ext_c_idx, ext_rest) =>
            let aux_c_ci = load(list_lookup(top, aux_c_idx));
            let ext_c_ci = load(list_lookup(top, ext_c_idx));
            match aux_c_ci {
              KConstantInfo.Ctor(_, aux_c_ty, _, _, _, _, _) =>
                match ext_c_ci {
                  KConstantInfo.Ctor(_, ext_c_ty, _, _, _, _, _) =>
                    let body = synth_aux_ctor_ty(ext_c_ty, ext_n_params, spec_params);
                    let synth_c = wrap_foralls(body, block_param_doms);
                    match compare_kexpr(synth_c, aux_c_ty) {
                      1 => compare_aux_ctors(aux_rest, ext_rest, ext_n_params, spec_params,
                                             block_param_doms, top),
                      _ => 0,
                    },
                  _ => 0,
                },
              _ => 0,
            },
        },
    }
  }

  fn populate_rules(rec_idx: G, ind_idx: G, ctor_indices: List‹G›,
                    n_params: G, n_motives: G, n_minors: G,
                    ind_lvls: G, univ_offset: G,
                    motive_doms: List‹KExpr›, minor_doms: List‹KExpr›,
                    param_doms: List‹KExpr›, peer_recs: List‹G›,
                    flat: List‹(G, G, List‹KExpr›, List‹KLevel›)›,
                    flat_idxs: List‹G›, flat_own_params: List‹G›,
                    is_aux: G, spec_params: List‹KExpr›,
                    occurrence_us: List‹KLevel›,
                    top: List‹&KConstantInfo›, addrs: List‹Addr›,
                    ctor_pos: G) -> List‹KRecRule› {
    match load(ctor_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(ctor_idx, rest) =>
        let ctor_ci = load(list_lookup(top, ctor_idx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, owning_ind, _, _, n_fields, _) =>
            let rhs = build_rule_rhs(rec_idx, owning_ind, ctor_idx, ctor_ty, ctor_pos,
                                     n_params, n_motives, n_minors, ind_lvls, univ_offset,
                                     motive_doms, minor_doms, param_doms, peer_recs,
                                     flat, flat_idxs, flat_own_params,
                                     is_aux, spec_params, occurrence_us, top, addrs);
            let rule = KRecRule.Mk(ctor_idx, n_fields, rhs);
            store(ListNode.Cons(rule,
              populate_rules(rec_idx, ind_idx, rest, n_params, n_motives, n_minors,
                             ind_lvls, univ_offset, motive_doms, minor_doms, param_doms,
                             peer_recs, flat, flat_idxs, flat_own_params,
                             is_aux, spec_params, occurrence_us,
                             top, addrs, ctor_pos + 1))),
        },
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:2817-2924 fn build_direct_ih.
  -- Forall-wrapped recursive fields wrap IH body in matching Foralls.
  -- For each rec field, motive at offset motive_base + member_local_idx so
  -- multi-member blocks correctly select per-member motives.
  -- Mirror src/ix/kernel/inductive.rs:2817-2924 fn build_direct_ih.
  -- Each rec-field's dom may be written via reducible defs (e.g.
  -- `constType (n α) (n α)`); we WHNF before peeling Foralls and before
  -- collecting the inner spine so the head/args reflect the *true*
  -- inductive occurrence rather than the surface alias.
  fn build_ih_doms(rec_indices: List‹G›, rec_member_idxs: List‹G›,
                   field_doms: List‹KExpr›,
                   flat_own_params: List‹G›,
                   motive_base: G, n_fields: G,
                   minor_saved: G, types: List‹KExpr›,
                   top: List‹&KConstantInfo›, addrs: List‹Addr›,
                   k: G) -> List‹KExpr› {
    match load(rec_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(field_idx, rest) =>
        let mem_idx = list_lookup(rec_member_idxs, k);
        let target_n_params = list_lookup(flat_own_params, mem_idx);
        let depth = minor_saved + n_fields + k;
        let dom = list_lookup(field_doms, field_idx);
        let dom_lifted = expr_lift(dom, (n_fields - field_idx) + k, 0);
        let dom_w = whnf(dom_lifted, types, top, addrs);
        match peel_leading_foralls(dom_w) {
          (forall_doms, inner_body_raw) =>
            let inner_types = list_concat(list_reverse(forall_doms), types);
            let inner_body = whnf(inner_body_raw, inner_types, top, addrs);
            let n_xs = list_length(forall_doms);
            let inner_depth = depth + n_xs;
            let motive_bvar = (inner_depth - 1) - (motive_base + mem_idx);
            let field_bvar = (inner_depth - 1) - (minor_saved + field_idx);
            match collect_spine(inner_body) {
              (_h, dom_args) =>
                let idx_args = list_drop(dom_args, target_n_params);
                let motive_ref = store(KExprNode.BVar(motive_bvar));
                let with_indices = apply_spine(motive_ref, idx_args);
                let field_ref = store(KExprNode.BVar(field_bvar));
                let field_app = build_apply_xs(field_ref, n_xs, 0);
                let ih_body = store(KExprNode.App(with_indices, field_app));
                let ih_dom = wrap_foralls(ih_body, forall_doms);
                store(ListNode.Cons(ih_dom,
                  build_ih_doms(rest, rec_member_idxs, field_doms, flat_own_params,
                                motive_base, n_fields, minor_saved, types, top, addrs, k + 1))),
            },
        },
    }
  }

  -- Mirror: src/ix/kernel/inductive.rs:216-250 mutual peer-loop +
  -- 1660-1700 fn check_param_agreement.
  -- Solo (block_addr = [0;32]) is no-op.
  fn check_block_peer_param_agreement(self_pos: G, self_ty: KExpr,
                                      self_n_params: G, self_n_indices: G,
                                      block_addr: Addr,
                                      top: List‹&KConstantInfo›,
                                      addrs: List‹Addr›) {
    match address_eq(block_addr, store([0u8; 32])) {
      1 => (),
      0 => peer_param_loop(self_pos, self_ty, self_n_params, self_n_indices,
                           block_addr, top, top, addrs, 0),
    }
  }

  fn peer_param_loop(self_pos: G, self_ty: KExpr,
                     self_n_params: G, self_n_indices: G,
                     block_addr: Addr,
                     consts: List‹&KConstantInfo›,
                     top: List‹&KConstantInfo›,
                     addrs: List‹Addr›, idx: G) {
    match load(consts) {
      ListNode.Nil => (),
      ListNode.Cons(&ci, rest) =>
        match ci {
          KConstantInfo.Induct(_, peer_ty, peer_n_params, peer_n_indices, _, _, peer_block_addr) =>
            let same_block = address_eq(peer_block_addr, block_addr);
            let is_self = eq_zero(idx - self_pos);
            let should_check = same_block * (1 - is_self);
            match should_check {
              1 =>
                -- S3b: param-count + param-domain agreement.
                assert_eq!(peer_n_params, self_n_params);
                check_param_agreement(self_ty, peer_ty, self_n_params, top, addrs);
                -- S3: result-universe agreement. Mirror src/ix/kernel/inductive.rs:228-237.
                let self_lvl = get_result_sort_level(self_ty, self_n_params + self_n_indices);
                let peer_lvl = get_result_sort_level(peer_ty, peer_n_params + peer_n_indices);
                assert_eq!(level_equal(self_lvl, peer_lvl), 1);
                peer_param_loop(self_pos, self_ty, self_n_params, self_n_indices,
                                block_addr, rest, top, addrs, idx + 1),
              0 =>
                peer_param_loop(self_pos, self_ty, self_n_params, self_n_indices,
                                block_addr, rest, top, addrs, idx + 1),
            },
          _ =>
            peer_param_loop(self_pos, self_ty, self_n_params, self_n_indices,
                            block_addr, rest, top, addrs, idx + 1),
        },
    }
  }

  -- Walk first n Foralls of both types asserting domain def-eq under the
  -- accumulated param-binder context.
  fn check_param_agreement(ta: KExpr, tb: KExpr, n: G,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    check_param_agreement_go(ta, tb, n, store(ListNode.Nil), top, addrs)
  }

  fn check_param_agreement_go(ta: KExpr, tb: KExpr, n: G,
                              types: List‹KExpr›,
                              top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    match n {
      0 => (),
      _ =>
        match load(ta) {
          KExprNode.Forall(da, ba) =>
            match load(tb) {
              KExprNode.Forall(db, bb) =>
                let eq = k_is_def_eq(da, db, types, top, addrs);
                assert_eq!(eq, 1);
                let inner = store(ListNode.Cons(da, types));
                check_param_agreement_go(ba, bb, n - 1, inner, top, addrs),
            },
        },
    }
  }
⟧

end IxVM

end
