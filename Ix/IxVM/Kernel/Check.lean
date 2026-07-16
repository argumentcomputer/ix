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
      KConstantInfo.Induct(_, _, _, _, _, u, _) => u,
      KConstantInfo.Ctor(_, _, _, _, _, _, u) => u,
      KConstantInfo.Rec(_, _, _, _, _, _, _, _, u, _) => u,
    }
  }

  -- Mirror: src/ix/kernel/check.rs Safe→Unsafe transitive rejection.
  -- Walks every Const(idx, _) in `e`; returns 0 if any target const is
  -- unsafe, 1 otherwise. Used only when the calling const is itself safe.
  fn safe_refs_only(e: KExpr, top: List‹&KConstantInfo›) -> G {
    match load(e) {
      KExprNode.BVar(_) => 1,
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
  #[group=cold] fn validate_univ_params_seen(u: KLevel, bound: G) {
    match load(u) {
      KLevelNode.Zero => (),
      KLevelNode.Succ(inner) => validate_univ_params_seen(inner, bound),
      KLevelNode.Max(a, b) =>
        validate_univ_params_seen(a, bound);
        validate_univ_params_seen(b, bound),
      KLevelNode.IMax(a, b) =>
        validate_univ_params_seen(a, bound);
        validate_univ_params_seen(b, bound),
      KLevelNode.Param(i) =>
        assert_eq!(u32_less_than(i, bound), 1);
        (),
    }
  }

  fn validate_univ_params_list(lvls: List‹KLevel›, bound: G) {
    match load(lvls) {
      ListNode.Nil => (),
      ListNode.Cons(u, rest) =>
        validate_univ_params_seen(u, bound);
        validate_univ_params_list(rest, bound),
    }
  }

  -- Mirror: src/ix/kernel/check.rs:494-570 fn validate_expr_well_scoped.
  -- Walks `e` checking `BVar(i) < depth`, Const universe-arity match, and
  -- recurses into universes via `validate_univ_params_seen`.
  fn validate_expr_well_scoped(e: KExpr, depth: G, bound: G,
                                top: List‹&KConstantInfo›) {
    match load(e) {
      KExprNode.BVar(i) =>
        assert_eq!(u32_less_than(i, depth), 1);
        (),
      KExprNode.Srt(l) => validate_univ_params_seen(l, bound),
      KExprNode.Const(idx, lvls) =>
        let ci = load(list_lookup(top, idx));
        let expected = const_num_lvls(ci);
        assert_eq!(list_length(lvls), expected);
        validate_univ_params_list(lvls, bound),
      KExprNode.App(f, a) =>
        validate_expr_well_scoped(f, depth, bound, top);
        validate_expr_well_scoped(a, depth, bound, top),
      KExprNode.Lam(t, b) =>
        validate_expr_well_scoped(t, depth, bound, top);
        validate_expr_well_scoped(b, depth + 1, bound, top),
      KExprNode.Forall(t, b) =>
        validate_expr_well_scoped(t, depth, bound, top);
        validate_expr_well_scoped(b, depth + 1, bound, top),
      KExprNode.Let(t, v, b) =>
        validate_expr_well_scoped(t, depth, bound, top);
        validate_expr_well_scoped(v, depth, bound, top);
        validate_expr_well_scoped(b, depth + 1, bound, top),
      KExprNode.Lit(_) => (),
      KExprNode.Proj(_, _, val) =>
        validate_expr_well_scoped(val, depth, bound, top),
    }
  }

  -- Mirror: src/ix/kernel/check.rs:422-478 fn validate_const_well_scoped.
  -- Validates type + variant-specific value/rules. Rec rules carry rhs each.
  fn validate_const_well_scoped(ci: KConstantInfo, top: List‹&KConstantInfo›) {
    let bound = const_num_lvls(ci);
    let ty = const_type_of(ci);
    validate_expr_well_scoped(ty, 0, bound, top);
    match ci {
      KConstantInfo.Defn(_, _, val, _, _) =>
        validate_expr_well_scoped(val, 0, bound, top),
      KConstantInfo.Thm(_, _, val) =>
        validate_expr_well_scoped(val, 0, bound, top),
      KConstantInfo.Opaque(_, _, val, _) =>
        validate_expr_well_scoped(val, 0, bound, top),
      KConstantInfo.Rec(_, _, _, _, _, _, rules, _, _, _) =>
        validate_recr_rules(rules, bound, top),
      _ => (),
    }
  }

  #[group=cold] fn validate_recr_rules(rules: List‹KRecRule›, bound: G,
                          top: List‹&KConstantInfo›) {
    match load(rules) {
      ListNode.Nil => (),
      ListNode.Cons(rule, rest) =>
        match rule {
          KRecRule.Mk(_, _, rhs) =>
            validate_expr_well_scoped(rhs, 0, bound, top);
            validate_recr_rules(rest, bound, top),
        },
    }
  }

  -- Mirror: src/ix/kernel/check.rs:678-720 fn check_eq_type.
  -- Asserts the Eq inductive in `top` has 1 universe param, 2 params, and
  -- exactly one ctor whose address matches `eq_refl_addr()`.
  #[group=cold] fn check_eq_type(top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    let eq_idx = find_addr_idx(eq_addr(), addrs, 0);
    let eq_ci = load(list_lookup(top, eq_idx));
    match eq_ci {
      KConstantInfo.Induct(num_lvls, _, n_params, _, ctor_indices, _, _) =>
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
    validate_const_well_scoped(ci, top);
    let u = is_unsafe_ci(ci);
    match ci {
      KConstantInfo.Axiom(_, ty, _) =>
        k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_safety(u, ty, top);
        (),

      KConstantInfo.Defn(_, ty, val, _, _) =>
        k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_safety(u, ty, top);
        assert_safety(u, val, top);
        k_check(val, ty, store(ListNode.Nil), top, addrs);
        (),

      KConstantInfo.Thm(_, ty, val) =>
        -- Mirror: src/ix/kernel/check.rs:135. Theorem type must be Sort 0.
        let lvl = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_eq!(level_equal(lvl, store(KLevelNode.Zero)), 1);
        assert_safety(u, ty, top);
        assert_safety(u, val, top);
        k_check(val, ty, store(ListNode.Nil), top, addrs);
        (),

      KConstantInfo.Opaque(_, ty, val, is_unsafe) =>
        k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_safety(u, ty, top);
        assert_safety(u, val, top);
        match is_unsafe {
          1 => (),
          0 =>
            k_check(val, ty, store(ListNode.Nil), top, addrs);
            (),
        },

      KConstantInfo.Quot(num_lvls, ty, kind) =>
        k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_safety(u, ty, top);
        -- Mirror: src/ix/kernel/check.rs:606-675 fn check_quot.
        -- Validate kind ↔ address consistency, universe-param count per
        -- variant, and forall-binder count.
        let self_addr = list_lookup(addrs, pos);
        check_quot(self_addr, kind, num_lvls, ty, top, addrs);
        (),

      KConstantInfo.Induct(_, ty, n_params, n_indices, _,
                          _, block_addr) =>
        k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_safety(u, ty, top);
        check_block_peer_param_agreement(pos, ty, n_params, n_indices,
                                                  block_addr, top, addrs);
        -- Self-contained inductive validation: result sort + the full
        -- per-ctor gauntlet (param agreement, return type, field
        -- universes, positivity). Without it, subject-only checking
        -- (arena `verify_const`) accepts an inductive whose badness
        -- lives in a ctor const. Mirror: check_inductive_member walks
        -- its ctors.
        check_inductive_shape(pos, top, addrs);
        let block_idxs = derive_block_member_idxs(pos, top);
        validate_block_auxes(block_idxs, top);
        -- The former H1 declared-vs-computed is_rec check is gone with the
        -- Ixon recr flag: there is no declared value to verify. is_rec is
        -- computed on demand (`computed_is_rec_ind`) wherever it matters
        -- (struct-eta / unit-like gates), so an adversary has nothing to
        -- forge. Mirror: check_inductive after `Ixon: drop recr/refl/nested`.
        (),

      -- Ctor cross-ref + return-type + field-universe + strict-positivity
      -- (positivity walks mutual + nested via derive_block_member_idxs).
      KConstantInfo.Ctor(_, ty, induct_idx, _, num_params, num_fields, _) =>
        k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_safety(u, ty, top);
        check_ctor_against_inductive_member(pos, ci, top);
        let ind_ci = load(list_lookup(top, induct_idx));
        match ind_ci {
          KConstantInfo.Induct(ind_num_lvls, ind_ty, ind_n_params, ind_n_indices, _, _, _) =>
            assert_eq!(num_params, ind_n_params);
            -- A1 defense-in-depth: ctor's leading param domains must match
            -- parent inductive's. Mirror src/ix/kernel/inductive.rs:283,393.
            check_param_agreement(ind_ty, ty, ind_n_params, top, addrs);
            check_ctor_return_type(ty, num_params, ind_n_indices, num_fields,
                                           induct_idx, ind_num_lvls, top);
            let ind_level = get_result_sort_level(ind_ty, ind_n_params + ind_n_indices);
            check_field_universes(ty, num_params, ind_level,
                                          store(ListNode.Nil), top, addrs);
            check_positivity(ty, num_params, induct_idx, store(ListNode.Nil), top, addrs);
            (),
        },

      KConstantInfo.Rec(_, ty, _, _, _, _, _, _, _, _) =>
        k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        assert_safety(u, ty, top);
        check_recursor_member(pos, ci, top, addrs);
        (),
    }
  }

  -- Mirror: src/ix/kernel/check.rs:606-675 fn check_quot.
  -- Validates quot variant consistency: address ↔ kind match, universe
  -- param count, and at-least-N forall binders for the type.
  #[group=cold] fn check_quot(self_addr: Addr, kind: QuotKind, num_lvls: G, ty: KExpr,
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
        check_eq_type(top, addrs);
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
  #[group=cold] fn count_foralls_at_least(ty: KExpr, n: G, seen: G) -> G {
    match n - seen {
      0 => 1,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) => count_foralls_at_least(body, n, seen + 1),
          _ => 0,
        },
    }
  }

  #[group=cold] fn check_all(consts: List‹&KConstantInfo›, top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    check_canonical_block_sort(top);
    check_all_iter(consts, top, addrs, 0)
  }

  fn check_all_iter(consts: List‹&KConstantInfo›, top: List‹&KConstantInfo›,
                    addrs: List‹Addr›, pos: G) {
    match load(consts) {
      ListNode.Nil => (),
      ListNode.Cons(&ci, rest) =>
        check_const(ci, pos, top, addrs);
        check_all_iter(rest, top, addrs, pos + 1),
    }
  }
⟧

end IxVM

end
