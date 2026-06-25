module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Whnf
public import Ix.IxVM.Kernel.Infer
public import Ix.IxVM.Kernel.DefEq

public section

namespace IxVM

/-! ## Per-constant type checking

Mirrors `src/ix/kernel/check.rs::check_const_member` (line 95+).

Per `KConstantInfo` variant:

* `Axio { ty }` → infer ty, ensure_sort.
* `Defn { ty, val }` → infer ty (ensure_sort), infer val, is_def_eq val_ty ty.
* `Thm { ty, val }` → as Defn, plus assert ty's level is Prop (Sort 0).
* `Opaque { ty, val, is_unsafe }` → ensure_sort ty; if !is_unsafe, also
  infer val and is_def_eq.
* `Quot { ty }` → infer ty, ensure_sort.
* `Indc { ty }` → infer ty, ensure_sort.
* `Ctor { ty }` → infer ty, ensure_sort.
* `Recr { ty }` → infer ty, ensure_sort.

Top-level entry: `check_all` walks the kernel const list and calls
`check_const` per element. Failures `assert_eq!(0, 1)` to fail the proof.
-/

def check := ⟦
  -- Mirror: each KConstantInfo's unsafe flag (Defn = DefinitionSafety,
  -- others = G). Returns 1 if unsafe, 0 if safe. Thm and Quot are always safe.
  fn is_unsafe_ci(ci: KConstantInfo) -> G {
    match ci {
      KConstantInfo.Axiom(_, _, u) => u,
      KConstantInfo.Defn(_, _, _, s, _) =>
        match s {
          DefinitionSafety.Unsafe => 1,
          _ => 0,
        },
      KConstantInfo.Thm(_, _, _) => 0,
      KConstantInfo.Opaque(_, _, _, u) => u,
      KConstantInfo.Quot(_, _, _) => 0,
      KConstantInfo.Induct(_, _, _, _, _, _, _, u, _, _) => u,
      KConstantInfo.Ctor(_, _, _, _, _, _, u) => u,
      KConstantInfo.Rec(_, _, _, _, _, _, _, _, u, _) => u,
    }
  }

  -- Mirror: src/ix/kernel/check.rs Safe→Unsafe transitive rejection.
  -- Walks every Const(idx, _) in `e`; returns 0 if any target const is
  -- unsafe, 1 otherwise. Used only when the calling const is itself safe.
  fn safe_refs_only(e: KExpr, top: List‹&KConstantInfo›) -> G {
    match load(e) {
      KExprNode.BVar(_, _) => 1,
      KExprNode.Srt(_) => 1,
      KExprNode.Const(idx, _) =>
        let ci = load(list_lookup(top, idx));
        1 - is_unsafe_ci(ci),
      KExprNode.App(f, a) =>
        safe_refs_only(f, top) * safe_refs_only(a, top),
      KExprNode.Lam(t, b) =>
        safe_refs_only(t, top) * safe_refs_only(b, top),
      KExprNode.Forall(t, b) =>
        safe_refs_only(t, top) * safe_refs_only(b, top),
      KExprNode.Let(t, v, b) =>
        safe_refs_only(t, top) * safe_refs_only(v, top) * safe_refs_only(b, top),
      KExprNode.Lit(_) => 1,
      KExprNode.Proj(_, _, e1) => safe_refs_only(e1, top),
    }
  }

  -- Assert that a Safe-classified const has no unsafe refs in `e`.
  -- For unsafe-classified consts, this is a no-op.
  fn assert_safety(self_unsafe: G, e: KExpr, top: List‹&KConstantInfo›) {
    match self_unsafe {
      1 => (),
      0 =>
        let ok = safe_refs_only(e, top);
        assert_eq!(ok, 1);
        (),
    }
  }

  -- Mirror: src/ix/kernel/check.rs:572-598 fn validate_univ_params_seen.
  -- Walks a KLevel asserting `Param(i)` has `i < bound`. Aiur's `store`/
  -- `load` deduplication subsumes Rust's seen-set.
  fn validate_univ_params_seen(u: KLevel, bound: G) {
    match u {
      KLevel.Zero => (),
      KLevel.Succ(&inner) => validate_univ_params_seen(inner, bound),
      KLevel.Max(&a, &b) =>
        let _ = validate_univ_params_seen(a, bound);
        validate_univ_params_seen(b, bound),
      KLevel.IMax(&a, &b) =>
        let _ = validate_univ_params_seen(a, bound);
        validate_univ_params_seen(b, bound),
      KLevel.Param(i) =>
        assert_eq!(u32_less_than(i, bound), 1);
        (),
    }
  }

  fn validate_univ_params_list(lvls: List‹&KLevel›, bound: G) {
    match load(lvls) {
      ListNode.Nil => (),
      ListNode.Cons(&u, rest) =>
        let _ = validate_univ_params_seen(u, bound);
        validate_univ_params_list(rest, bound),
    }
  }

  -- ============================================================================
  -- correct_expr: the typed-BVar fill-in pass, which ALSO validates.
  --
  -- Ingress (convert_expr) leaves every BVar with a placeholder annotation, and
  -- keeps the heavy Ixon→KExpr translation context-free so Aiur dedups shared
  -- subterms. `correct_expr` is the single light walk that (a) rebuilds each
  -- BVar with its canonical occurrence-valid type `lift(types[i], i+1, 0)` (via
  -- `types_lookup`, the same form infer uses), AND (b) performs the well-scoped
  -- validation that `validate_expr_well_scoped` used to do separately:
  --   * no loose bvars (`BVar(i) < depth`),
  --   * Const universe-arity match + universe-param bounds.
  -- One walk, both jobs (per the design note: the corrector can validate too).
  -- Mirror of src/ix/kernel/check.rs:494-570 (validation) fused with the
  -- annotation fill-in (docs/ixvm-context-free-inference.org).
  fn correct_expr(e: KExpr, types: List‹KExpr›, depth: G, bound: G,
                  top: List‹&KConstantInfo›) -> KExpr {
    match load(e) {
      KExprNode.BVar(i, _) =>
        assert_eq!(u32_less_than(i, depth), 1);
        store(KExprNode.BVar(i, types_lookup(types, i))),
      KExprNode.Srt(&l) =>
        let _ = validate_univ_params_seen(l, bound);
        e,
      KExprNode.Const(idx, lvls) =>
        let ci = load(list_lookup(top, idx));
        assert_eq!(list_length(lvls), const_num_lvls(ci));
        let _ = validate_univ_params_list(lvls, bound);
        e,
      KExprNode.App(f, a) =>
        store(KExprNode.App(correct_expr(f, types, depth, bound, top),
                            correct_expr(a, types, depth, bound, top))),
      KExprNode.Lam(t, b) =>
        let kt = correct_expr(t, types, depth, bound, top);
        store(KExprNode.Lam(kt,
          correct_expr(b, store(ListNode.Cons(kt, types)), depth + 1, bound, top))),
      KExprNode.Forall(t, b) =>
        let kt = correct_expr(t, types, depth, bound, top);
        store(KExprNode.Forall(kt,
          correct_expr(b, store(ListNode.Cons(kt, types)), depth + 1, bound, top))),
      KExprNode.Let(t, v, b) =>
        let kt = correct_expr(t, types, depth, bound, top);
        let kv = correct_expr(v, types, depth, bound, top);
        store(KExprNode.Let(kt, kv,
          correct_expr(b, store(ListNode.Cons(kt, types)), depth + 1, bound, top))),
      KExprNode.Lit(_) => e,
      KExprNode.Proj(tidx, fidx, val) =>
        store(KExprNode.Proj(tidx, fidx, correct_expr(val, types, depth, bound, top))),
    }
  }

  fn correct_rules(rules: List‹KRecRule›, bound: G,
                   top: List‹&KConstantInfo›) -> List‹KRecRule› {
    match load(rules) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(rule, rest) =>
        match rule {
          KRecRule.Mk(ctor, nf, rhs) =>
            store(ListNode.Cons(
              KRecRule.Mk(ctor, nf,
                          correct_expr(rhs, store(ListNode.Nil), 0, bound, top)),
              correct_rules(rest, bound, top))),
        },
    }
  }

  -- Correct + validate one constant's type / value / rec-rule rhs. Const bodies
  -- are closed, so the walk starts with the empty context (depth 0).
  fn correct_const_info(ci: KConstantInfo, top: List‹&KConstantInfo›) -> KConstantInfo {
    let bound = const_num_lvls(ci);
    match ci {
      KConstantInfo.Axiom(n, ty, u) =>
        KConstantInfo.Axiom(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top), u),
      KConstantInfo.Defn(n, ty, val, s, h) =>
        KConstantInfo.Defn(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top),
                           correct_expr(val, store(ListNode.Nil), 0, bound, top), s, h),
      KConstantInfo.Thm(n, ty, val) =>
        KConstantInfo.Thm(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top),
                          correct_expr(val, store(ListNode.Nil), 0, bound, top)),
      KConstantInfo.Opaque(n, ty, val, u) =>
        KConstantInfo.Opaque(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top),
                             correct_expr(val, store(ListNode.Nil), 0, bound, top), u),
      KConstantInfo.Quot(n, ty, k) =>
        KConstantInfo.Quot(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top), k),
      KConstantInfo.Induct(n, ty, np, ni, cis, r, rf, u, ne, ba) =>
        KConstantInfo.Induct(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top),
                             np, ni, cis, r, rf, u, ne, ba),
      KConstantInfo.Ctor(n, ty, ii, cidx, np, nf, u) =>
        KConstantInfo.Ctor(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top),
                           ii, cidx, np, nf, u),
      KConstantInfo.Rec(n, ty, np, ni, nm, nmin, rules, k, u, ba) =>
        KConstantInfo.Rec(n, correct_expr(ty, store(ListNode.Nil), 0, bound, top),
                          np, ni, nm, nmin, correct_rules(rules, bound, top), k, u, ba),
    }
  }

  -- Correct + validate the WHOLE constant table once, before checking, so
  -- context-free inference (which reads dep types out of `top`) sees correct
  -- annotations everywhere. `top` is read only for Const universe-arity (the
  -- num_lvls field is unaffected by correction, so the uncorrected table works).
  fn correct_all(consts: List‹&KConstantInfo›, top: List‹&KConstantInfo›) -> List‹&KConstantInfo› {
    match load(consts) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(&ci, rest) =>
        store(ListNode.Cons(store(correct_const_info(ci, top)), correct_all(rest, top))),
    }
  }

  -- Mirror: src/ix/kernel/check.rs:678-720 fn check_eq_type.
  -- Asserts the Eq inductive in `top` has 1 universe param, 2 params, and
  -- exactly one ctor whose address matches `eq_refl_addr()`.
  fn check_eq_type(top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    let eq_idx = find_addr_idx(eq_addr(), addrs, 0);
    let eq_ci = load(list_lookup(top, eq_idx));
    match eq_ci {
      KConstantInfo.Induct(num_lvls, _, n_params, _, ctor_indices, _, _, _, _, _) =>
        assert_eq!(num_lvls, 1);
        assert_eq!(n_params, 2);
        assert_eq!(list_length(ctor_indices), 1);
        let ctor_pos = list_lookup(ctor_indices, 0);
        let ctor_addr = list_lookup(addrs, ctor_pos);
        assert_eq!(address_eq(ctor_addr, eq_refl_addr()), 1);
        (),
    }
  }

  -- ============================================================================
  -- check_const: dispatch per KConstantInfo variant.
  -- ============================================================================
  fn check_const(ci: KConstantInfo, pos: G, top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    let u = is_unsafe_ci(ci);
    match ci {
      KConstantInfo.Axiom(_, ty, _) =>
        let _ = k_ensure_sort(ty, top, addrs);
        let _ = assert_safety(u, ty, top);
        (),

      KConstantInfo.Defn(_, ty, val, _, _) =>
        let _ = k_ensure_sort(ty, top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = assert_safety(u, val, top);
        let _ = k_check(val, ty, top, addrs);
        (),

      KConstantInfo.Thm(_, ty, val) =>
        -- Mirror: src/ix/kernel/check.rs:135. Theorem type must be Sort 0.
        let lvl = k_ensure_sort(ty, top, addrs);
        assert_eq!(level_equal(load(lvl), KLevel.Zero), 1);
        let _ = assert_safety(u, ty, top);
        let _ = assert_safety(u, val, top);
        let _ = k_check(val, ty, top, addrs);
        (),

      KConstantInfo.Opaque(_, ty, val, is_unsafe) =>
        let _ = k_ensure_sort(ty, top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = assert_safety(u, val, top);
        match is_unsafe {
          1 => (),
          0 =>
            let _ = k_check(val, ty, top, addrs);
            (),
        },

      KConstantInfo.Quot(num_lvls, ty, kind) =>
        let _ = k_ensure_sort(ty, top, addrs);
        let _ = assert_safety(u, ty, top);
        -- Mirror: src/ix/kernel/check.rs:606-675 fn check_quot.
        -- Validate kind ↔ address consistency, universe-param count per
        -- variant, and forall-binder count.
        let self_addr = list_lookup(addrs, pos);
        let _ = check_quot(self_addr, kind, num_lvls, ty, top, addrs);
        (),

      KConstantInfo.Induct(_, ty, n_params, n_indices, ctor_indices,
                          is_rec, _, _, _, block_addr) =>
        let _ = k_ensure_sort(ty, top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = check_block_peer_param_agreement(pos, ty, n_params, n_indices,
                                                  block_addr, top, addrs);
        let block_idxs = derive_block_member_idxs(pos, top);
        let _ = validate_block_auxes(block_idxs, top);
        -- H1: constructively recompute is_rec by scanning ctor field doms
        -- for block-member references. Mirror src/ix/kernel/inductive.rs:309-315.
        -- Without this, an adversary could set is_rec=0 on a recursive
        -- 1-ctor inductive to enable struct-eta on a recursive structure.
        let computed_is_rec = compute_is_rec(ctor_indices, n_params, block_idxs, top);
        assert_eq!(is_rec, computed_is_rec);
        (),

      -- Ctor cross-ref + return-type + field-universe + strict-positivity
      -- (positivity walks mutual + nested via derive_block_member_idxs).
      KConstantInfo.Ctor(_, ty, induct_idx, _, num_params, num_fields, _) =>
        let _ = k_ensure_sort(ty, top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = check_ctor_against_inductive_member(pos, ci, top);
        let ind_ci = load(list_lookup(top, induct_idx));
        match ind_ci {
          KConstantInfo.Induct(ind_num_lvls, ind_ty, ind_n_params, ind_n_indices, _, _, _, _, _, _) =>
            assert_eq!(num_params, ind_n_params);
            -- A1 defense-in-depth: ctor's leading param domains must match
            -- parent inductive's. Mirror src/ix/kernel/inductive.rs:283,393.
            let _ = check_param_agreement(ind_ty, ty, ind_n_params, top, addrs);
            let _ = check_ctor_return_type(ty, num_params, ind_n_indices, num_fields,
                                           induct_idx, ind_num_lvls);
            let ind_level = get_result_sort_level(ind_ty, ind_n_params + ind_n_indices);
            let _ = check_field_universes(ty, num_params, ind_level,
                                          top, addrs);
            let _ = check_positivity(ty, num_params, induct_idx, top, addrs);
            (),
        },

      KConstantInfo.Rec(_, ty, _, _, _, _, _, _, _, _) =>
        let _ = k_ensure_sort(ty, top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = check_recursor_member(pos, ci, top, addrs);
        (),
    }
  }

  -- Mirror: src/ix/kernel/check.rs:606-675 fn check_quot.
  -- Validates quot variant consistency: address ↔ kind match, universe
  -- param count, and at-least-N forall binders for the type.
  fn check_quot(self_addr: Addr, kind: QuotKind, num_lvls: G, ty: KExpr,
                 top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    -- Address ↔ kind consistency + per-variant (lvls, foralls) expectations.
    -- Type/Ctor/Ind = 1 lvl; Lift = 2 lvls.
    -- Foralls: Type=2, Ctor=3, Lift=6, Ind=5.
    let pair = match kind {
      QuotKind.Typ =>
        assert_eq!(address_eq(self_addr, quot_type_addr()), 1);
        (1, 2),
      QuotKind.Ctor =>
        assert_eq!(address_eq(self_addr, quot_ctor_addr()), 1);
        (1, 3),
      QuotKind.Lift =>
        assert_eq!(address_eq(self_addr, quot_lift_addr()), 1);
        -- Mirror: src/ix/kernel/check.rs:651-653. Lift requires Eq type
        -- to be properly formed (Quot.lift uses Eq in its reduction rule).
        let _ = check_eq_type(top, addrs);
        (2, 6),
      QuotKind.Ind =>
        assert_eq!(address_eq(self_addr, quot_ind_addr()), 1);
        (1, 5),
    };
    match pair {
      (expected_lvls, expected_foralls) =>
        assert_eq!(num_lvls, expected_lvls);
        assert_eq!(count_foralls_at_least(ty, expected_foralls, 0), 1);
        (),
    }
  }

  -- Returns 1 iff `ty` has at least `n` leading Foralls.
  fn count_foralls_at_least(ty: KExpr, n: G, seen: G) -> G {
    match n - seen {
      0 => 1,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) => count_foralls_at_least(body, n, seen + 1),
          _ => 0,
        },
    }
  }

  fn check_all(consts: List‹&KConstantInfo›, top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    let _ = check_canonical_block_sort(top);
    check_all_iter(consts, top, addrs, 0)
  }

  fn check_all_iter(consts: List‹&KConstantInfo›, top: List‹&KConstantInfo›,
                    addrs: List‹Addr›, pos: G) {
    match load(consts) {
      ListNode.Nil => (),
      ListNode.Cons(&ci, rest) =>
        let _ = check_const(ci, pos, top, addrs);
        check_all_iter(rest, top, addrs, pos + 1),
    }
  }
⟧

end IxVM

end
