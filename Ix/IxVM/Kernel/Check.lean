module
public import Ix.Aiur.Meta

public section

namespace IxVM

/-! ## Check — the per-constant typechecker

`check_const` dispatches on the constant's variant and is the single
entry point for "is this constant well-typed": Axiom, Defn, Thm, Opaque,
Quot, Induct, Ctor, and Rec. The declaration-kind-specific machinery —
inductive shape, the constructor gauntlet (return type, parameter
agreement, field universes, strict positivity), large-eliminator
classification, and recursor canonicality — lives in this module too.

`assert_safety` enforces that a Safe-classified constant references only
Safe constants: it walks the expression and resolves each `Const(addr)`
through `get_ci`. That resolution is what makes the check affordable
here — `get_ci` is memoized and the check only needs each referenced
constant's safety classification, not its body.

Scope validation: `validate_univ_params_seen` universe-only —
included here (no addr work).
-/

set_option maxRecDepth 32768 in
def check := ⟦
  -- Mirror is_unsafe_ci: 1 if a SAFE constant may not reference it, 0
  -- otherwise. Thm/Quot always safe.
  --
  -- `Partial` counts alongside `Unsafe`, matching the reference's
  -- "safe definition references partial definition" rejection
  -- (crates/kernel/src/check.rs). This is load-bearing rather than
  -- cosmetic: a partial definition may reference ITSELF (see the recur
  -- slot in Ingress), and `k_infer` discharges a `Const` against its
  -- declared type without checking it, so `partial def bad : False := bad`
  -- typechecks in isolation. Barring safe code from referencing it is what
  -- keeps that out of the trusted fragment.
  fn is_unsafe_ci(ci: KConstantInfo) -> G {
    match ci {
      KConstantInfo.Axiom(_, _, u) => u,
      KConstantInfo.Defn(_, _, _, s, _) =>
        match s {
          DefinitionSafety.Safe => 0,
          _ => 1,
        },
      KConstantInfo.Thm(_, _, _) => 0,
      KConstantInfo.Opaque(_, _, _, u) => u,
      KConstantInfo.Quot(_, _, _) => 0,
      KConstantInfo.Induct(_, _, _, _, _, u, _, _) => u,
      KConstantInfo.Ctor(_, _, _, _, _, _, _, u) => u,
      KConstantInfo.Rec(_, _, _, _, _, _, _, _, u, _, _) => u,
    }
  }

  -- Safe→Unsafe transitive rejection. Walks every Const(addr, _) in `e`;
  -- returns 0 if any target const is unsafe, 1 otherwise. Used only when
  -- the calling const is itself safe. Refs resolve via get_ci.
  fn safe_refs_only(e: KExpr) -> G {
    match load(e) {
      KExprNode.BVar(_) => 1,
      KExprNode.Srt(_) => 1,
      KExprNode.Const(caddr, _) =>
        let ci = load(get_ci(caddr));
        1 - is_unsafe_ci(ci),
      KExprNode.App(f, a) =>
        safe_refs_only(f) * safe_refs_only(a),
      KExprNode.Lam(t, b) =>
        safe_refs_only(t) * safe_refs_only(b),
      KExprNode.Forall(t, b) =>
        safe_refs_only(t) * safe_refs_only(b),
      KExprNode.Let(t, v, b) =>
        safe_refs_only(t) * safe_refs_only(v) * safe_refs_only(b),
      KExprNode.Lit(_) => 1,
      KExprNode.Proj(_, _, e1) => safe_refs_only(e1),
    }
  }

  -- Assert a Safe-classified const has no unsafe refs in `e`.
  -- For unsafe self, no-op.
  fn assert_safety(self_unsafe: G, e: KExpr) {
    match self_unsafe {
      1 => (),
      _ =>
        assert_eq!(safe_refs_only(e), 1,
          "safe constant references an unsafe constant");
        (),
    }
  }

  -- Mirror crates/kernel/src/check.rs fn validate_univ_params_seen.
  -- Walks a KLevel asserting `Param(i)` has `i < bound`. Aiur's `store`/
  -- `load` deduplication subsumes Rust's seen-set.
  fn validate_univ_params_seen(u: KLevel, bound: G) {
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
        assert_eq!(u32_less_than(i, bound), 1,
          "universe param index out of range");
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

  -- Walk `e` checking BVar depth + Const universe arity + Sort
  -- level params bounded. Recurses via `get_ci` on each Const.
  fn validate_expr_well_scoped(e: KExpr, depth: G, bound: G) {
    match load(e) {
      KExprNode.BVar(i) =>
        assert_eq!(u32_less_than(i, depth), 1,
          "loose bound variable: BVar index exceeds binder depth");
        (),
      KExprNode.Srt(l) => validate_univ_params_seen(l, bound),
      KExprNode.Const(addr, lvls) =>
        let ci = load(get_ci(addr));
        let expected = const_num_lvls(ci);
        assert_eq!(list_length(lvls), expected,
          "Const applied to wrong number of universe levels");
        validate_univ_params_list(lvls, bound),
      KExprNode.App(f, a) =>
        validate_expr_well_scoped(f, depth, bound);
        validate_expr_well_scoped(a, depth, bound),
      KExprNode.Lam(t, b) =>
        validate_expr_well_scoped(t, depth, bound);
        validate_expr_well_scoped(b, depth + 1, bound),
      KExprNode.Forall(t, b) =>
        validate_expr_well_scoped(t, depth, bound);
        validate_expr_well_scoped(b, depth + 1, bound),
      KExprNode.Let(t, v, b) =>
        validate_expr_well_scoped(t, depth, bound);
        validate_expr_well_scoped(v, depth, bound);
        validate_expr_well_scoped(b, depth + 1, bound),
      KExprNode.Lit(_) => (),
      KExprNode.Proj(_, _, e1) =>
        validate_expr_well_scoped(e1, depth, bound),
    }
  }

  -- Type-check one constant at `addr` given its KConstantInfo.
  --  handles Axiom / Defn / Thm / Opaque / Quot. Ind/Ctor/Rec
  -- deferred to .
  fn quot_type_addr() -> Addr {
    store([0xabu8, 0x68u8, 0x2cu8, 0x17u8, 0x78u8, 0xa1u8, 0x7bu8, 0xbeu8,
     0xaeu8, 0x40u8, 0x32u8, 0x97u8, 0x4du8, 0xf3u8, 0x64u8, 0x47u8,
     0xceu8, 0x8bu8, 0xfcu8, 0xabu8, 0x67u8, 0x64u8, 0xa3u8, 0x6du8,
     0x37u8, 0x85u8, 0x66u8, 0xe3u8, 0xadu8, 0x63u8, 0xcau8, 0xb8u8])
  }

  fn quot_ctor_addr() -> Addr {
    store([0x88u8, 0x26u8, 0x66u8, 0x77u8, 0xfeu8, 0xe7u8, 0x74u8, 0xd1u8,
     0x09u8, 0x86u8, 0x7eu8, 0x4bu8, 0x22u8, 0x40u8, 0x28u8, 0x1au8,
     0xa2u8, 0xeeu8, 0x12u8, 0xd9u8, 0x79u8, 0x20u8, 0xc1u8, 0x17u8,
     0x1cu8, 0xf5u8, 0xc1u8, 0xf6u8, 0xc8u8, 0x7du8, 0xecu8, 0xf6u8])
  }

  fn quot_lift_addr() -> Addr {
    store([0x8du8, 0xc4u8, 0xa9u8, 0x75u8, 0x27u8, 0x81u8, 0x2fu8, 0x8bu8,
     0x78u8, 0x17u8, 0xb7u8, 0x7cu8, 0xd0u8, 0x79u8, 0xacu8, 0xe6u8,
     0x14u8, 0x50u8, 0xaau8, 0x01u8, 0x85u8, 0xacu8, 0x58u8, 0x85u8,
     0x66u8, 0x1eu8, 0xc2u8, 0xacu8, 0xbau8, 0x8bu8, 0x7bu8, 0xd0u8])
  }

  fn quot_ind_addr() -> Addr {
    store([0x12u8, 0x49u8, 0x84u8, 0xbcu8, 0xb9u8, 0x52u8, 0x08u8, 0xa0u8,
     0xf3u8, 0x0bu8, 0xb6u8, 0x9du8, 0x67u8, 0x36u8, 0xd3u8, 0xd5u8,
     0x94u8, 0x04u8, 0xe1u8, 0x15u8, 0xe2u8, 0x20u8, 0x20u8, 0x43u8,
     0xfdu8, 0xa3u8, 0xd3u8, 0x4eu8, 0x01u8, 0xb0u8, 0xadu8, 0x16u8])
  }

  -- Returns 1 iff `ty` has at least `n` leading Foralls.
  fn count_foralls_at_least(ty: KExpr, n: G, seen: G) -> G {
    match n - seen {
      0 => 1,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            count_foralls_at_least(body, n, seen + 1),
          _ => 0,
        },
    }
  }

  -- Mirror check_eq_type: assert Eq inductive shape (1 lvl, 2 params,
  -- 1 ctor = Eq.refl). the kernel's KConstantInfo.Induct doesn't store
  -- ctor_indices; we assert (num_lvls, n_params, num_ctors) then trust
  -- the ctor identity check to fire when Eq.refl itself is checked as a
  -- closure member (via check_ctor_return_type, which is  item 3).
  -- Adversarial Eq → Quot.Lift unsound reduction only if Eq is also
  -- forged in the closure; per-const gauntlet closes that.
  fn check_eq_type() {
    let eq_addr = store([0x03u8, 0x6bu8, 0x63u8, 0xd5u8, 0xccu8, 0x09u8, 0x61u8, 0xe9u8,
                          0x20u8, 0xdeu8, 0xe5u8, 0x0eu8, 0x73u8, 0x64u8, 0xecu8, 0x0du8,
                          0xd3u8, 0xf9u8, 0xc3u8, 0x8au8, 0x9cu8, 0xacu8, 0xe4u8, 0x0eu8,
                          0x51u8, 0x3bu8, 0x38u8, 0x35u8, 0xdeu8, 0xc8u8, 0xe0u8, 0xc9u8]);
    let eq_ci = load(get_ci(eq_addr));
    match eq_ci {
      KConstantInfo.Induct(num_lvls, _, n_params, _, num_ctors, _, _, _) =>
        assert_eq!(num_lvls, 1, "Eq inductive: wrong universe param count");
        assert_eq!(n_params, 2, "Eq inductive: wrong parameter count");
        assert_eq!(num_ctors, 1, "Eq inductive: wrong constructor count");
        (),
    }
  }

  -- Mirror check_quot: address ↔ kind consistency + (expected_lvls,
  -- expected_foralls) per variant. Quot.Lift extra: Eq inductive
  -- well-shaped.
  fn check_quot(self_addr: Addr, kind: QuotKind,
                    num_lvls: G, ty: KExpr) {
    let pair = match kind {
      QuotKind.Typ =>
        assert_eq!(address_eq(self_addr, quot_type_addr()), 1,
          "Quot.Typ declared at a non-canonical address");
        (1, 2),
      QuotKind.Ctor =>
        assert_eq!(address_eq(self_addr, quot_ctor_addr()), 1,
          "Quot.mk declared at a non-canonical address");
        (1, 3),
      QuotKind.Lift =>
        assert_eq!(address_eq(self_addr, quot_lift_addr()), 1,
          "Quot.lift declared at a non-canonical address");
        check_eq_type();
        (2, 6),
      QuotKind.Ind =>
        assert_eq!(address_eq(self_addr, quot_ind_addr()), 1,
          "Quot.ind declared at a non-canonical address");
        (1, 5),
    };
    match pair {
      (expected_lvls, expected_foralls) =>
        assert_eq!(num_lvls, expected_lvls,
          "Quot constant: wrong universe param count for its kind");
        assert_eq!(count_foralls_at_least(ty, expected_foralls, 0), 1,
          "Quot constant: type has too few foralls for its kind");
        (),
    }
  }

  -- ============================================================================
  -- Ctor gauntlet — the checks a constructor must survive.
  --   check_ctor_return_type — assert the peeled body is headed by THIS
  --     inductive (via assert_return_head_is_parent), with matching
  --     universe params, the correct BVar param spine, and no index
  --     argument mentioning the inductive block (index positivity).
  --   check_param_agreement — walk n Foralls of both types, k_is_def_eq
  --     each domain under accumulated types.
  --   check_field_universes — post-params, each field domain's sort
  --     level ≤ ind_level. Skipped for Prop inductives.
  --   get_result_sort_level — peel n Foralls (whnf per step), return Sort's level.
  -- ============================================================================

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

  fn peel_n_lams(e: KExpr, n: G) -> KExpr {
    match n {
      0 => e,
      _ =>
        match load(e) {
          KExprNode.Lam(_, body) => peel_n_lams(body, n - 1),
        },
    }
  }

  -- Tolerant: peel up to n Lams, stop early on non-Lam.
  fn peel_n_lams_tol(e: KExpr, n: G, peeled: G) -> (KExpr, G) {
    match n {
      0 => (e, peeled),
      _ =>
        match load(e) {
          KExprNode.Lam(_, body) => peel_n_lams_tol(body, n - 1, peeled + 1),
          _ => (e, peeled),
        },
    }
  }

  -- Each `lvls[i]` must be `Param(expected_start + i)` for i in 0..count.
  fn assert_lvls_are_params(lvls: List‹KLevel›, count: G, idx: G) {
    match count {
      0 =>
        assert_eq!(list_length(lvls), 0,
          "more universe levels than the inductive declares");
        (),
      _ =>
        match load(lvls) {
          ListNode.Cons(l, rest) =>
            match load(l) {
              KLevelNode.Param(i) =>
                assert_eq!(i, idx,
                  "ctor return type: universe level is not Param(i) in order");
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
    match n_params - i {
      0 => (),
      _ =>
        match load(args) {
          ListNode.Cons(arg, rest) =>
            match load(arg) {
              KExprNode.BVar(j) =>
                assert_eq!(j, ((n_fields + n_params) - 1) - i,
                  "ctor return type: param arg is not the expected param BVar");
                assert_first_args_are_param_bvars(rest, n_params, n_fields, i + 1);
                (),
            },
        },
    }
  }

  -- Mirror crates/kernel/src/inductive.rs check_ctor_return_type.
  -- Validates that a ctor's declared type, after peeling
  -- `n_params + n_fields` Foralls, is a syntactic `Indc(params, indices)`
  -- application:
  -- * head is `Const(ind_idx, lvls)`
  -- * `lvls.len() == ind_num_lvls`
  -- * each `lvls[i]` is `Param(i)`
  -- * spine args count is `n_params + n_indices`
  -- * first `n_params` args are the param BVars (de Bruijn equivalents
  -- of Rust's param fvars at line 1986-1994).
  --
  -- Shapes that cannot occur have no match arm at all: an unmatched value
  -- aborts the Aiur execution, which is the kernel's reject. An arm whose
  -- only job is to fail is strictly worse — it widens the circuit on every
  -- row to buy an error message on a path that rejects either way.
  --
  -- The peeled return head must be THIS inductive: its KCI must be an
  -- Induct stored at (block_addr, ind_idx). Without it the head is
  -- constrained only to be SOME Const of matching universe arity, so a
  -- ctor of `I` may declare `mk : ... -> J params indices` for a
  -- different `J` — e.g. a mutual peer. `check_param_agreement` does not
  -- cover this: it compares only the first `n_params` forall domains and
  -- says nothing about the return head.
  fn assert_return_head_is_parent(caddr: Addr, block_addr: Addr,
                                       ind_idx: G) {
    let ci = load(get_ci(caddr));
    match ci {
      KConstantInfo.Induct(_, _, _, _, _, _, ba, ii) =>
        assert_eq!(address_eq(ba, block_addr), 1,
          "ctor return head belongs to a different block");
        assert_eq!(ii, ind_idx,
          "ctor return head is a different member of the block");
        (),
    }
  }

  fn check_ctor_return_type(ctor_ty: KExpr, n_params: G,
                                 n_indices: G, n_fields: G,
                                 ind_num_lvls: G, block_addr: Addr,
                                 ind_idx: G) {
    let body = peel_n_foralls(ctor_ty, n_params + n_fields);
    match collect_spine(body) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(head_addr, lvls) =>
            assert_return_head_is_parent(head_addr, block_addr, ind_idx);
            assert_lvls_are_params(lvls, ind_num_lvls, 0);
            assert_eq!(list_length(args), n_params + n_indices,
              "ctor return type: wrong number of spine arguments");
            assert_first_args_are_param_bvars(args, n_params, n_fields, 0);
            -- Index args must not mention block inductives — rejects
            -- `mk : I (I x)`, a reflexive occurrence in INDEX position.
            -- Field positions are covered by check_positivity; a ctor
            -- with zero fields has none, so this is the only gate that
            -- sees it. Mirror Inductive.lean:52-56.
            let idx_args = list_drop(args, n_params);
            let block_addrs = store(ListNode.Cons(block_addr,
                                                   store(ListNode.Nil)));
            assert_eq!(list_any_mentions_block(idx_args, block_addrs), 0,
              "ctor return type: reflexive occurrence in an index argument");
            (),
        },
    }
  }

  fn check_param_agreement_go(ta: KExpr, tb: KExpr, n: G,
                                   types: List‹KExpr›) {
    match n {
      0 => (),
      _ =>
        match load(ta) {
          KExprNode.Forall(da, ba) =>
            match load(tb) {
              KExprNode.Forall(db, bb) =>
                let eq = k_is_def_eq(da, db, types);
                assert_eq!(eq, 1,
                  "ctor parameter type disagrees with the inductive's");
                let inner = store(ListNode.Cons(da, types));
                check_param_agreement_go(ba, bb, n - 1, inner),
            },
        },
    }
  }

  -- Walk first n Foralls of both types asserting domain def-eq under the
  -- accumulated param-binder context.
  fn check_param_agreement(ta: KExpr, tb: KExpr, n: G) {
    check_param_agreement_go(ta, tb, n, store(ListNode.Nil))
  }

  -- Peel n (params + indices) Foralls; body must be Srt(l). Returns l.
  -- whnf per step: index binders can hide under defs.
  fn get_result_sort_level(ind_ty: KExpr, n: G,
                                types: List‹KExpr›) -> KLevel {
    let w = whnf(ind_ty, types);
    match n {
      0 =>
        match load(w) {
          KExprNode.Srt(l) => l,
        },
      _ =>
        match load(w) {
          KExprNode.Forall(dom, body) =>
            get_result_sort_level(body, n - 1,
              store(ListNode.Cons(dom, types))),
        },
    }
  }

  fn check_field_universes_inner(ty: KExpr, ind_level: KLevel,
                                      types: List‹KExpr›) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let dom_level = k_ensure_sort(dom, types);
        assert_eq!(level_leq(dom_level, ind_level), 1,
          "ctor field lives in a universe above the inductive's");
        check_field_universes_inner(body, ind_level,
          store(ListNode.Cons(dom, types))),
      _ => (),
    }
  }

  fn check_field_universes_skip_params(ctor_ty: KExpr, n_params: G,
                                            ind_level: KLevel,
                                            types: List‹KExpr›) {
    match n_params {
      0 => check_field_universes_inner(ctor_ty, ind_level, types),
      _ =>
        match load(ctor_ty) {
          KExprNode.Forall(dom, body) =>
            check_field_universes_skip_params(body, n_params - 1,
              ind_level, store(ListNode.Cons(dom, types))),
        },
    }
  }

  -- Skipped for Prop (ind_level = Zero).
  fn check_field_universes(ctor_ty: KExpr, n_params: G,
                                 ind_level: KLevel) {
    match load(ind_level) {
      KLevelNode.Zero => (),
      _ => check_field_universes_skip_params(ctor_ty, n_params,
                                                  ind_level, store(ListNode.Nil)),
    }
  }

  -- Fetch a constructor's parent inductive KCI. A Ctor stores its parent
  -- as (block_addr, ind_idx) rather than a direct addr, so resolution
  -- goes through the block's inductive projection wrapper.
  fn ctor_parent_ind_ci(block_addr: Addr, ind_idx: G)
                              -> &KConstantInfo {
    get_ci_iprj(block_addr, ind_idx)
  }

  -- ============================================================================
  -- Strict positivity.
  --
  -- Block membership is tracked by block_addr: a `Const(caddr, _)` is a
  -- peer of block_addr iff its KCI is an Inductive whose stored
  -- block_addr equals ours. Standalone inductives use their own addr as
  -- block_addr, so the same test covers both cases.
  --
  -- block_addrs: List<Addr> starts as the singleton [outer]
  -- (`check_positivity`) and is extended with a nested inductive's own
  -- block each time `check_positivity_aug` descends into it, so an
  -- occurrence is negative if it hits ANY enclosing block, not just the
  -- innermost. That growth is also what makes the descent terminate —
  -- see `check_nested_ctors_positivity`.
  -- ============================================================================

  fn addr_list_contains(xs: List‹Addr›, target: Addr) -> G {
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(a, rest) =>
        match address_eq(a, target) {
          1 => 1,
          _ => addr_list_contains(rest, target),
        },
    }
  }

  -- Query: does `caddr`'s KCI classify it as a peer inductive of any
  -- block in block_addrs? A Const is a peer iff its KCI is Induct AND its
  -- stored block_addr matches (mutual peer).
  fn caddr_is_peer(caddr: Addr, block_addrs: List‹Addr›) -> G {
    let ci = load(get_ci(caddr));
    match ci {
      KConstantInfo.Induct(_, _, _, _, _, _, ba, _) =>
        addr_list_contains(block_addrs, ba),
      _ => 0,
    }
  }

  fn expr_mentions_block(e: KExpr, block_addrs: List‹Addr›) -> G {
    match load(e) {
      KExprNode.BVar(_) => 0,
      KExprNode.Srt(_) => 0,
      KExprNode.Const(caddr, _) => caddr_is_peer(caddr, block_addrs),
      KExprNode.App(f, a) =>
        match expr_mentions_block(f, block_addrs) {
          1 => 1,
          _ => expr_mentions_block(a, block_addrs),
        },
      KExprNode.Lam(t, b) =>
        match expr_mentions_block(t, block_addrs) {
          1 => 1,
          _ => expr_mentions_block(b, block_addrs),
        },
      KExprNode.Forall(t, b) =>
        match expr_mentions_block(t, block_addrs) {
          1 => 1,
          _ => expr_mentions_block(b, block_addrs),
        },
      KExprNode.Let(t, v, b) =>
        match expr_mentions_block(t, block_addrs) {
          1 => 1,
          _ =>
            match expr_mentions_block(v, block_addrs) {
              1 => 1,
              _ => expr_mentions_block(b, block_addrs),
            },
        },
      KExprNode.Lit(_) => 0,
      KExprNode.Proj(_, _, e1) => expr_mentions_block(e1, block_addrs),
    }
  }

  fn list_any_mentions_block(es: List‹KExpr›,
                                  block_addrs: List‹Addr›) -> G {
    match load(es) {
      ListNode.Nil => 0,
      ListNode.Cons(e, rest) =>
        match expr_mentions_block(e, block_addrs) {
          1 => 1,
          _ => list_any_mentions_block(rest, block_addrs),
        },
    }
  }

  -- Like `peel_n_foralls_tolerant` but accumulates each binder's domain into
  -- the types context so subsequent WHNF calls have the right local context.
  fn peel_n_foralls_with_types(e: KExpr, n: G,
                                    types: List‹KExpr›) -> (KExpr, List‹KExpr›) {
    match n {
      0 => (e, types),
      _ =>
        match load(e) {
          KExprNode.Forall(dom, body) =>
            let t2 = store(ListNode.Cons(dom, types));
            peel_n_foralls_with_types(body, n - 1, t2),
          _ => (e, types),
        },
    }
  }

  -- Positivity check on one field's domain type.
  -- If dom doesn't mention any block member, trivially positive.
  -- If it does, whnf and inspect: a Forall with block-mentioning-body
  -- must NOT mention block in its own domain (else negative occurrence);
  -- an inductive spine head must be either a peer (block member — OK
  -- direct occurrence) or a nested inductive whose non-param args don't
  -- mention block.
  -- The i-th parameter argument of a recursive occurrence must be the
  -- i-th parameter BINDER. Parameters are peeled first, so in a context
  -- of `depth` binders the i-th (outermost-first) sits at
  -- `BVar(depth - 1 - i)` — the same arithmetic
  -- `assert_first_args_are_param_bvars` uses for the return type, where
  -- `depth` is `n_fields + n_params`.
  fn assert_occ_param_bvars(args: List‹KExpr›, n_params: G, depth: G,
                                 i: G) {
    match n_params - i {
      0 => (),
      _ =>
        match load(args) {
          ListNode.Cons(arg, rest) =>
            match load(arg) {
              KExprNode.BVar(j) =>
                assert_eq!(j, (depth - 1) - i,
                  "recursive occurrence: parameter arg is not the parameter binder");
                assert_occ_param_bvars(rest, n_params, depth, i + 1),
            },
        },
    }
  }

  -- A direct recursive occurrence must be a VALID application of the
  -- inductive, not merely headed by it. Mirrors what
  -- `check_ctor_return_type` already demands of the return type, and
  -- what Lean requires of every occurrence (`is_valid_ind_app`,
  -- explicitly `check_uniform_params` / `check_ind_app_idxs` since
  -- #14582):
  --
  --   * universe args are the declaration's own `Param(i)` sequence, so
  --     `J.{u}` cannot host a field at `J.{0}`;
  --   * the occurrence is fully applied, `n_params + n_indices` args;
  --   * parameter args are the parameter binders, so `I α` cannot host a
  --     field at `I False` — the recursor built for that applies
  --     `motive : I α → _` to a field of type `I False`;
  --   * index args do not mention the block (lean4 #2125). The return
  --     type's indices are checked in `check_ctor_return_type`; nothing
  --     covered a field's until now.
  fn check_valid_ind_app(caddr: Addr, us: List‹KLevel›,
                              args: List‹KExpr›, block_addrs: List‹Addr›,
                              depth: G) {
    let ci = load(get_ci(caddr));
    match ci {
      KConstantInfo.Induct(occ_nlvls, _, occ_params, occ_indices,
                            _, _, _, _) =>
        assert_lvls_are_params(us, occ_nlvls, 0);
        assert_eq!(list_length(args), occ_params + occ_indices,
          "recursive occurrence is not fully applied");
        assert_occ_param_bvars(args, occ_params, depth, 0);
        assert_eq!(list_any_mentions_block(list_drop(args, occ_params),
                                                block_addrs), 0,
          "recursive occurrence: index argument mentions the block");
        (),
    }
  }

  -- `check_params` is 1 on the direct path, where the block's parameters
  -- are still the outermost binders of `types` and the uniformity check
  -- above is meaningful. The nested descent
  -- (`check_nested_ctors_positivity`) substitutes the parameter
  -- ARGUMENTS away and restarts from an empty context, so there are no
  -- parameter binders left to match and the occurrence's args are
  -- arbitrary terms; it passes 0 and keeps the old head-identity accept.
  fn check_positivity_aug(dom: KExpr, block_addrs: List‹Addr›,
                               types: List‹KExpr›, check_params: G) {
    match expr_mentions_block(dom, block_addrs) {
      0 => (),
      _ =>
        let dom_w = whnf(dom, types);
        match load(dom_w) {
          KExprNode.Forall(idom, ibody) =>
            assert_eq!(expr_mentions_block(idom, block_addrs), 0,
              "strict positivity: block occurs left of an arrow");
            let t2 = store(ListNode.Cons(idom, types));
            check_positivity_aug(ibody, block_addrs, t2, check_params),
          _ =>
            match collect_spine(dom_w) {
              (head, args) =>
                match load(head) {
                  KExprNode.Const(caddr, us) =>
                    match caddr_is_peer(caddr, block_addrs) {
                      1 =>
                        match check_params {
                          1 =>
                            check_valid_ind_app(caddr, us, args,
                              block_addrs, list_length(types)),
                          _ => (),
                        },
                      _ =>
                        let ci = load(get_ci(caddr));
                        match ci {
                          KConstantInfo.Induct(_, _, n_ctor_params,
                                                 _, ext_num_ctors, _,
                                                 ext_block_addr, ext_ind_idx) =>
                            let after_params = list_drop(args, n_ctor_params);
                            assert_eq!(list_any_mentions_block(after_params,
                                                                    block_addrs), 0,
                              "strict positivity: block occurs in a nested inductive's index args");
                            -- Descend into the NESTED inductive's own
                            -- constructors under an augmented block set.
                            -- Without this, `Host | mk : Bad2 -> Host` is
                            -- accepted whenever `Bad2 | mk : (Bad2 -> Empty)
                            -- -> Bad2` is itself never checked — the
                            -- negative occurrence lives inside the ext, not
                            -- in Host's own field.
                            --
                            -- Terminates because `aug` only grows: a field
                            -- mentioning an already-tracked block hits the
                            -- `caddr_is_peer` arm above and stops, and the
                            -- number of distinct reachable blocks is finite.
                            let aug = store(ListNode.Cons(ext_block_addr,
                                                              block_addrs));
                            let rev_params = list_reverse(
                              list_take(args, n_ctor_params));
                            check_nested_ctors_positivity(ext_block_addr,
                              ext_ind_idx, ext_num_ctors, aug, 0,
                              n_ctor_params, rev_params),
                        },
                    },
                },
            },
        },
    }
  }

  -- Walk every constructor of the nested inductive at
  -- (block_addr, ind_idx), checking its fields under the augmented block
  -- set. The ctors are reached by index through the block's projection
  -- wrappers.
  -- `rev_params` are the nested inductive's actual parameter ARGUMENTS,
  -- reversed, and `n_params` is how many there are.
  --
  -- Substituting them is what makes this check mean anything. A nested
  -- constructor's fields mention the inductive's parameters as bound
  -- variables, so descending into the raw declared type asks whether the
  -- block occurs in `BVar 0` — it never does, and every parameter
  -- position passes vacuously. The occurrence being hunted lives in the
  -- ARGUMENT that was substituted for that parameter. Concretely, for
  -- `Inner α | mk : (α → False) → Inner α` used as `Inner Host`, the
  -- negative occurrence of `Host` only appears once `α := Host`.
  --
  -- Mirrors `check_nested_ctor_fields` (crates/kernel/src/inductive.rs):
  -- strip `n_params` foralls, then simultaneously substitute at depth 0.
  -- After stripping, `BVar 0` is the LAST (innermost) parameter, so the
  -- argument list is reversed — `expr_inst_many` maps `substs[i]` to
  -- `BVar(depth + i)`, the same convention as `simul_subst`.
  fn check_nested_ctors_positivity(block_addr: Addr, ind_idx: G,
                                        num_ctors: G, aug: List‹Addr›,
                                        cidx: G, n_params: G,
                                        rev_params: List‹KExpr›) {
    match num_ctors - cidx {
      0 => (),
      _ =>
        let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, cidx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _, _) =>
            match peel_n_foralls_with_types(ctor_ty, n_params,
                                                 store(ListNode.Nil)) {
              (body, _) =>
                -- Parameters are substituted away, so the field walk
                -- starts with no binders in scope — and with no
                -- parameter binders to match, hence `check_params = 0`.
                check_positivity_fields(expr_inst_many(body, rev_params, 0),
                  aug, store(ListNode.Nil), 0);
                check_nested_ctors_positivity(block_addr, ind_idx,
                  num_ctors, aug, cidx + 1, n_params, rev_params),
            },
        },
    }
  }

  fn check_positivity_fields(ty: KExpr, block_addrs: List‹Addr›,
                                  types: List‹KExpr›, check_params: G) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        check_positivity_aug(dom, block_addrs, types, check_params);
        let t2 = store(ListNode.Cons(dom, types));
        check_positivity_fields(body, block_addrs, t2, check_params),
      _ => (),
    }
  }

  -- Mirror crates/kernel/src/inductive.rs check_positivity.
  -- Strict positivity: each ctor field's domain must not have any inductive
  -- of `ind_idx`'s mutual block in a negative position (left of an arrow).
  -- For mutual blocks, the initial positivity context is the full set of
  -- peer inductive idxs (derived via block_addr). Nested inductives are
  -- handled by augment_block_idxs walking ctor bodies recursively.
  fn check_positivity(ctor_ty: KExpr, n_params: G,
                          block_addr: Addr, types: List‹KExpr›) {
    let block_addrs = store(ListNode.Cons(block_addr, store(ListNode.Nil)));
    match peel_n_foralls_with_types(ctor_ty, n_params, types) {
      (body, types_after) =>
        check_positivity_fields(body, block_addrs, types_after, 1),
    }
  }

  -- Mirror Inductive.lean:73 check_inductive_shape.
  --
  -- Self-contained inductive validation: the inductive's own type must
  -- peel params+indices to a Sort, and EVERY constructor of the block
  -- runs the full gauntlet (identity, param agreement, return type,
  -- field universes, positivity).
  --
  -- Load-bearing for subject-only checking: an inductive whose badness
  -- lives in a ctor (negative occurrence, wrong ctor params, bad field
  -- universe) is only rejected if checking the INDUCTIVE walks its
  -- ctors. Without this the arena `verify_const` fixtures indNeg /
  -- inductWrongCtorParams / reflOccLeft / … are silently accepted.
  -- Ctors resolve through get_ci_cprj (memoized), so a block's
  -- shape check costs one pass regardless of how many members ask.
  fn check_inductive_shape(ty: KExpr, n_params: G, n_indices: G,
                                num_ctors: G, num_lvls: G,
                                block_addr: Addr, ind_idx: G,
                                is_unsafe: G) {
    let ind_level = get_result_sort_level(ty, n_params + n_indices,
                                               store(ListNode.Nil));
    check_inductive_shape_ctors(ty, n_params, n_indices, num_ctors,
                                     num_lvls, block_addr, ind_idx,
                                     ind_level, is_unsafe, 0)
  }

  fn check_inductive_shape_ctors(ind_ty: KExpr, n_params: G,
                                      n_indices: G, num_ctors: G,
                                      num_lvls: G, block_addr: Addr,
                                      ind_idx: G, ind_level: KLevel,
                                      is_unsafe: G, cidx: G) {
    match num_ctors - cidx {
      0 => (),
      _ =>
        let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, cidx));
        match ctor_ci {
          KConstantInfo.Ctor(_, cty, c_block, c_ind_idx, c_cidx,
                              c_np, c_nf, _) =>
            -- Identity: the ctor must point back at THIS inductive, at
            -- the position we asked for.
            assert_eq!(address_eq(c_block, block_addr), 1,
              "ctor belongs to a different block than its inductive");
            assert_eq!(c_ind_idx, ind_idx,
              "ctor points at a different member of the block");
            assert_eq!(c_cidx, cidx,
              "ctor's stored index differs from its position");
            assert_eq!(c_np, n_params,
              "ctor parameter count differs from the inductive's");
            check_param_agreement(ind_ty, cty, n_params);
            check_ctor_return_type(cty, c_np, n_indices, c_nf, num_lvls,
                                        block_addr, ind_idx);
            check_field_universes(cty, c_np, ind_level);
            -- Strict positivity is SKIPPED for unsafe inductives (mirror
            -- inductive.rs:441 "Lean skips positivity for unsafe
            -- inductives"). Running it anyway aborted on Batteries'
            -- `MLList.MLListImpl`, whose (legal-because-unsafe) ctor arg
            -- has a recursive occurrence under a BVar-headed application
            -- the positivity walker has no case for.
            match is_unsafe {
              0 => check_positivity(cty, c_np, block_addr,
                                         store(ListNode.Nil)),
              _ => (),
            };
            check_inductive_shape_ctors(ind_ty, n_params, n_indices,
                                             num_ctors, num_lvls,
                                             block_addr, ind_idx,
                                             ind_level, is_unsafe,
                                             cidx + 1),
        },
    }
  }

  -- Run the inductive shape gauntlet on an already-loaded Induct KCI.
  -- Used by the Rec arm, where the parent inductive is resolved from
  -- the recursor's motive spine rather than from check_const's subject.
  fn check_parent_inductive_shape(ind_ci: KConstantInfo) {
    match ind_ci {
      KConstantInfo.Induct(nlvls, ty, n_params, n_indices, num_ctors,
                            is_unsafe, block_addr, ind_idx) =>
        check_inductive_shape(ty, n_params, n_indices, num_ctors,
                                   nlvls, block_addr, ind_idx, is_unsafe),
      _ => (),
    }
  }

  -- Mirror Inductive.lean:3330-3378 check_block_peer_param_agreement.
  -- Solo (block_addr == self addr) is no-op. For Muts blocks, walk
  -- member list; for each Indc at position != self_ind_idx, resolve
  -- via get_ci_iprj (memoized) and:
  --   * n_params must match self's.
  --   * First n_params leading Foralls' domains def-eq via
  --     check_param_agreement.
  --   * Result-universe (post params+indices) equal.
  fn check_block_peer_param_agreement(ind_ci: KConstantInfo, addr: Addr) {
    match ind_ci {
      KConstantInfo.Induct(_, self_ty, self_np, self_ni, _, _,
                             block_addr, self_ind_idx) =>
        match address_eq(block_addr, addr) {
          1 => (),
          _ =>
            let block_c = load_verified_constant(block_addr);
            match block_c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.Muts(members) =>
                    peer_agree_walk(members, self_ty, self_np, self_ni,
                                         self_ind_idx, 0, block_addr),
                  _ => (),
                },
            },
        },
      _ => (),
    }
  }

  fn peer_agree_walk(members: List‹MutConst›, self_ty: KExpr,
                          self_np: G, self_ni: G,
                          self_ind_idx: G, pos: G, block_addr: Addr) {
    match load(members) {
      ListNode.Nil => (),
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Indc(_) =>
            let is_self = eq_zero(pos - self_ind_idx);
            match is_self {
              1 =>
                peer_agree_walk(rest, self_ty, self_np, self_ni,
                                     self_ind_idx, pos + 1, block_addr),
              _ =>
                let peer_ci = load(get_ci_iprj(block_addr, pos));
                match peer_ci {
                  KConstantInfo.Induct(_, peer_ty, peer_np, peer_ni,
                                         _, _, _, _) =>
                    assert_eq!(peer_np, self_np,
                      "mutual block peers disagree on parameter count");
                    check_param_agreement(self_ty, peer_ty, self_np);
                    let self_lvl = get_result_sort_level(self_ty,
                      self_np + self_ni, store(ListNode.Nil));
                    let peer_lvl = get_result_sort_level(peer_ty,
                      peer_np + peer_ni, store(ListNode.Nil));
                    assert_eq!(level_equal(self_lvl, peer_lvl), 1,
                      "mutual block peers land in different universes");
                    peer_agree_walk(rest, self_ty, self_np, self_ni,
                                         self_ind_idx, pos + 1, block_addr),
                  _ =>
                    peer_agree_walk(rest, self_ty, self_np, self_ni,
                                         self_ind_idx, pos + 1, block_addr),
                },
            },
          _ =>
            peer_agree_walk(rest, self_ty, self_np, self_ni,
                                 self_ind_idx, pos + 1, block_addr),
        },
    }
  }

  -- Large-eliminator classification. Returns 1 if the inductive with
  -- (result_level, num_ctors, and if num_ctors=1 its lone ctor) can
  -- target any universe; 0 if it must target Prop.
  -- Takes the single ctor's KCI directly rather than looking it up — the
  -- caller already resolved it via get_ci_cprj.
  fn is_large_eliminator(result_level: KLevel, num_ctors: G,
                              single_ctor_opt: (G, KConstantInfo),
                              is_solo: G) -> G {
    match level_is_not_zero(result_level) {
      1 => 1,
      _ =>
        -- Large elimination FROM Prop requires a single inductive in the
        -- block (mirror inductive.rs is_large_eliminator: "Must be a
        -- single inductive for large elimination from Prop"). Without
        -- this gate a mutual block of single-ctor Props (e.g. a mutual
        -- pair where each member's only ctor mentions the other) is
        -- misclassified as large-eliminating and the reconstructed
        -- motives land in Sort u against the declared Prop, rejecting
        -- the recursor. Non-Prop stays large above regardless of
        -- mutuality, matching the reference's ordering.
        match is_solo {
          0 => 0,
          _ =>
            match num_ctors {
              0 => 1,
              1 =>
                match single_ctor_opt {
                  (present, ctor_ci) =>
                    match present {
                      0 => 0,
                      _ =>
                        match ctor_ci {
                          KConstantInfo.Ctor(_, ctor_ty, _, _, _, n_params,
                                                n_fields, _) =>
                            match n_fields {
                              0 => 1,
                              _ => check_large_prop_ctor(ctor_ty, n_params,
                                                              n_fields,
                                                              store(ListNode.Nil)),
                            },
                          _ => 0,
                        },
                    },
                },
              _ => 0,
            },
        },
    }
  }

  -- Mirror crates/kernel/src/inductive.rs large-elim check on Prop
  -- single-ctor inductive. Walk past `n_params` Foralls (skipping params),
  -- then walk `n_fields` Foralls collecting de Bruijn indices of data fields
  -- (those whose domain has sort != 0). Body after walk is the ctor's return
  -- type; check each data field's BVar appears in the return-type's spine
  -- args. If all do → large eliminator.
  fn check_large_prop_ctor(ty: KExpr, n_params: G, n_fields: G,
                                types: List‹KExpr›) -> G {
    match n_params {
      0 =>
        check_large_walk_fields(ty, n_fields, 0, types,
                                     store(ListNode.Nil)),
      _ =>
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            let inner = store(ListNode.Cons(dom, types));
            check_large_prop_ctor(body, n_params - 1, n_fields, inner),
          _ => 0,
        },
    }
  }

  -- Walk `n_fields` Foralls, threading list of data-field BVars (de Bruijn
  -- indices in the post-walk ret context). After walk, collect ret spine
  -- args and verify every data BVar appears.
  fn check_large_walk_fields(ty: KExpr, n_fields: G, field_idx: G,
                                  types: List‹KExpr›,
                                  data_bvars: List‹G›) -> G {
    match n_fields - field_idx {
      0 =>
        match collect_spine(ty) {
          (_, args) => all_bvars_in_args(data_bvars, args),
        },
      _ =>
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            let lvl = k_ensure_sort(dom, types);
            let is_data = 1 - level_equal(lvl, store(KLevelNode.Zero));
            -- Parenthesized: Aiur `-` is right-associative, so the bare
            -- `n_fields - 1 - field_idx` reads as `n_fields - (1 - field_idx)`
            -- and is correct only at field_idx = 0. At field_idx = 1 it
            -- yields `n_fields` — the last param BVar, which the return
            -- spine is guaranteed to contain — so a data field that never
            -- appears in the return indices was counted as if it did, and
            -- the inductive was classified large-eliminating when it is not.
            let bvar_idx = (n_fields - 1) - field_idx;
            let new_bvars = match is_data {
              0 => data_bvars,
              _ => store(ListNode.Cons(bvar_idx, data_bvars)),
            };
            let inner = store(ListNode.Cons(dom, types));
            check_large_walk_fields(body, n_fields, field_idx + 1,
                                          inner, new_bvars),
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
          _ => all_bvars_in_args(rest, args),
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

  -- Mirror Inductive.lean:2009-2037 compute_k_target (the kernel port).
  -- K-target valid iff: solo block, result level == 0 (Prop), single
  -- ctor with 0 fields. Returns 1 if K-target, else 0.
  -- the kernel solo detection: parent inductive's block_addr == parent's own
  -- addr (Muts wrappers set block_addr = wrapper addr, standalone sets
  -- it to self). Additionally load Muts if present and check
  -- member-count == 1 for singleton-Muts case.
  fn compute_k_target(ind_ci: KConstantInfo, ind_addr: Addr) -> G {
    match ind_ci {
      KConstantInfo.Induct(_, ind_ty, n_params, n_indices, num_ctors,
                             _, block_addr, ind_idx) =>
        let is_solo = ind_is_solo(block_addr, ind_addr);
        match is_solo {
          0 => 0,
          _ =>
            let result_level = get_result_sort_level(ind_ty,
              n_params + n_indices, store(ListNode.Nil));
            match level_equal(result_level, store(KLevelNode.Zero)) {
              0 => 0,
              _ =>
                match num_ctors {
                  1 =>
                    let ctor_ci = load(get_ci_cprj(block_addr,
                      ind_idx, 0));
                    match ctor_ci {
                      KConstantInfo.Ctor(_, _, _, _, _, _, n_fields, _) =>
                        eq_zero(n_fields),
                      _ => 0,
                    },
                  _ => 0,
                },
            },
        },
      _ => 0,
    }
  }

  -- Solo iff (a) standalone (block_addr == self) OR
  -- (b) Muts wrapper containing exactly one Indc member.
  fn ind_is_solo(block_addr: Addr, ind_addr: Addr) -> G {
    match address_eq(block_addr, ind_addr) {
      1 => 1,
      _ =>
        let block_c = load_verified_constant(block_addr);
        match block_c {
          Constant.Mk(info, _, _, _) =>
            match info {
              ConstantInfo.Muts(members) => muts_indc_count_is_one(members, 0),
              _ => 0,
            },
        },
    }
  }

  fn is_muts_block(addr: Addr) -> G {
    let block_c = load_verified_constant(addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(_) => 1,
          _ => 0,
        },
    }
  }

  fn muts_indc_count_is_one(members: List‹MutConst›, count: G) -> G {
    match load(members) {
      ListNode.Nil =>
        match count {
          1 => 1,
          _ => 0,
        },
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Indc(_) => muts_indc_count_is_one(rest, count + 1),
          _ => muts_indc_count_is_one(rest, count),
        },
    }
  }

  -- Shape-level recursor validation: rule count plus k_flag consistency
  -- (the k_flag stored in the recursor's KCI must equal what
  -- compute_k_target says about its parent inductive).
  --
  -- This is weaker than full canonical-rules identity (build_flat_block +
  -- build_rec_type + populate_rules + compare_rules, which
  -- check_recursor_canonical_full does): it does not reconstruct the
  -- expected rules and compare them, so a rule with the right arity but a
  -- wrong right-hand side passes here. What it does catch:
  --   * Parent inductive (via block_addr + rec_idx) exists and is Induct.
  --   * Rules count matches parent's num_ctors — adversarial rules-count
  --     mismatch (fake extra ctor rule / missing rule) rejected.
  -- Canonical rules identity (iota-rhs shape verification) deferred; an
  -- adversarial recursor with type-checking but semantically-wrong rules
  -- surfaces at def_eq time when reducing `rec (ctor args)`.
  -- Extract parent inductive's addr from recursor's type. Mirror
  -- rec_to_ind_idx_with_ty: peel (params + motives + minors + indices)
  -- Foralls; next Forall's domain is `major`, a Const-headed spine of
  -- the parent inductive. Take head's caddr. Works for both standalone
  -- and Muts-wrapped recursors (the kernel addr-first — one path).
  fn rec_to_parent_addr(ty: KExpr, n_p: G, n_mot: G, n_min: G,
                             n_i: G) -> Addr {
    let skip = n_p + n_mot + n_min + n_i;
    let after_skip = peel_n_foralls(ty, skip);
    match load(after_skip) {
      KExprNode.Forall(major_ty, _) =>
        match collect_spine(major_ty) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(caddr, _) => caddr,
            },
        },
    }
  }

  -- Extract aux recursor's spec_params: peel outer Foralls to reach
  -- major, take spine[0..ext_np) of major's dom. For non-aux, returns
  -- []; for aux, returns the params the ext parent was applied with
  -- (e.g., Tree.rec_1 for List Tree: spec_params = [Tree]).
  -- Universe args of a nested occurrence, read off the head of the aux
  -- recursor's major premise. These are CONCRETE — the levels the
  -- occurrence was actually applied with — not the recursor's own shifted
  -- parameters. An original member's motive quantifies over the block's
  -- params, but an aux member's occurrence was fixed at the point of
  -- nesting, so rebuilding it from `univ_offset` names a different universe
  -- than the declared recursor does.
  fn extract_aux_occ_us(rec_ci: KConstantInfo) -> List‹KLevel› {
    match rec_ci {
      KConstantInfo.Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) =>
        let skip = ((np + nmot) + nmin) + ni;
        match load(peel_n_foralls(ty, skip)) {
          KExprNode.Forall(major_ty, _) =>
            match collect_spine(major_ty) {
              (head, _) =>
                match load(head) {
                  KExprNode.Const(_, us) => us,
                  _ => store(ListNode.Nil),
                },
            },
          _ => store(ListNode.Nil),
        },
      _ => store(ListNode.Nil),
    }
  }

  -- 1 iff every level is a bare Param. The flat-block machinery downstream
  -- assumes that shape; a concrete occurrence may legitimately carry Succ or
  -- Max levels, and those must not be fed into it.
  fn lvls_all_params(us: List‹KLevel›) -> G {
    match load(us) {
      ListNode.Nil => 1,
      ListNode.Cons(u, rest) =>
        match load(u) {
          KLevelNode.Param(_) => lvls_all_params(rest),
          _ => 0,
        },
    }
  }

  fn extract_aux_spec_params(ty: KExpr, n_p: G, n_mot: G, n_min: G,
                                   n_i: G, ext_np: G) -> List‹KExpr› {
    let skip = n_p + n_mot + n_min + n_i;
    let after_skip = peel_n_foralls(ty, skip);
    match load(after_skip) {
      KExprNode.Forall(major_ty, _) =>
        match collect_spine(major_ty) {
          (_head, args) =>
            -- De-lift to the recursor-param frame (block param j at
            -- BVar(n_p-1-j)) — the storage convention every consumer
            -- assumes. The args were read off the major premise, which
            -- sits n_mot + n_min + n_i binders above the params, so
            -- storing them raw leaves every consumer to re-derive that
            -- offset from data it does not have. Lowering here also
            -- makes the same occurrence found at two different field
            -- depths intern to the same pointer, which is what the
            -- spec_params_ptr_eq dedup relies on.
            spec_params_lower(list_take(args, ext_np),
              (n_mot + n_min) + n_i),
        },
    }
  }

  -- Lower each spec_param out of the major-premise frame into the
  -- recursor-param frame. Asserts rather than lowering blindly: a param
  -- arg that references a motive, minor, or index binder has no image in
  -- the param frame, and expr_lower would silently capture it.
  fn spec_params_lower(sps: List‹KExpr›, d: G) -> List‹KExpr› {
    match load(sps) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(sp, rest) =>
        assert_eq!(has_bvar_in_range(sp, 0, d), 0,
          "nested occurrence's parameter references a motive, minor, or index binder");
        store(ListNode.Cons(expr_lower(sp, d, 0),
                            spec_params_lower(rest, d))),
    }
  }

  -- ============================================================================
  -- Flat block construction.
  --
  -- A flat block is the list of members the recursor iterates over,
  -- comprising (a) originals: all Indc members of the rec's own Muts
  -- block, plus (b) auxes: nested-external inductive occurrences
  -- discovered by scanning member ctors for external Const-headed spines.
  --
  -- Each flat entry:
  --   (member_addr: Addr, is_aux: G, spec_params: List<KExpr>,
  --    occurrence_us: List<KLevel>)
  --
  -- For originals: member_addr = IPrj wrapper addr in the Muts block,
  -- is_aux = 0, spec_params = [], occurrence_us = [Param(univ_offset),
  -- Param(univ_offset+1), ..., Param(univ_offset+ind_nlvls-1)].
  --
  -- For auxes: member_addr = the EXT inductive's addr (from the nested
  -- occurrence), is_aux = 1, spec_params = the concrete substitution for
  -- ext parent's params (usually block members), occurrence_us = the
  -- universe args from the nested reference.
  --
  -- Standalone (non-Muts) blocks: single-entry with the standalone Ind's
  -- own addr, occurrence_us built from its stored nlvls.
  -- ============================================================================

  -- Build param-lvls range: [Param(start), Param(start+1), ..., Param(start+count-1)].
  fn build_param_lvls_range(start: G, count: G, i: G) -> List‹KLevel› {
    match count - i {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons(
          store(KLevelNode.Param(start + i)),
          build_param_lvls_range(start, count, i + 1))),
    }
  }

  -- Originals of a flat block: walk Muts Indc members, build entry per Indc.
  -- For standalone (non-Muts) blocks: single-entry with block_addr itself.
  fn build_flat_originals(block_addr: Addr, univ_offset: G)
                                -> List‹(Addr, G, List‹KExpr›, List‹KLevel›)› {
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            flat_originals_walk(members, members, block_addr,
              univ_offset, 0),
          _ =>
            -- Standalone: single entry with self addr; fetch nlvls
            -- via get_ci on block_addr (which resolves to this Ind).
            let ci = load(get_ci(block_addr));
            match ci {
              KConstantInfo.Induct(nlvls, _, _, _, _, _, _, _) =>
                let occ = build_param_lvls_range(univ_offset, nlvls, 0);
                store(ListNode.Cons(
                  (block_addr, 0, store(ListNode.Nil), occ),
                  store(ListNode.Nil))),
              _ => store(ListNode.Nil),
            },
        },
    }
  }

  fn flat_originals_walk(all_members: List‹MutConst›,
                              cur: List‹MutConst›, block_addr: Addr,
                              univ_offset: G, pos: G)
                              -> List‹(Addr, G, List‹KExpr›, List‹KLevel›)› {
    match load(cur) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Indc(_) =>
            let member_addr = projection_addr(all_members, block_addr, pos);
            let member_ci = load(get_ci_iprj(block_addr, pos));
            let nlvls = match member_ci {
              KConstantInfo.Induct(nl, _, _, _, _, _, _, _) => nl,
              _ => 0,
            };
            let occ = build_param_lvls_range(univ_offset, nlvls, 0);
            store(ListNode.Cons(
              (member_addr, 0, store(ListNode.Nil), occ),
              flat_originals_walk(all_members, rest, block_addr,
                univ_offset, pos + 1))),
          _ =>
            flat_originals_walk(all_members, rest, block_addr,
              univ_offset, pos + 1),
        },
    }
  }

  -- Detect aux entries by scanning Recr members of a Muts block. Each
  -- Recr whose parsed parent Ind is NOT a member of the same block is
  -- an aux (compiler-generated for nested-ext traversal). Parent's addr
  -- becomes the aux's target inductive; spec_params come from the aux
  -- Recr's ty major spine (first ext_np args).
  fn detect_aux_from_recrs(block_addr: Addr, univ_offset: G,
                                 originals: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›)
                                -> List‹(Addr, G, List‹KExpr›, List‹KLevel›)› {
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            aux_from_recrs_walk(members, members, block_addr,
              univ_offset, originals, 0),
          _ => store(ListNode.Nil),
        },
    }
  }

  -- Check if aux (parent_addr, spec_params) already present in flat_so_far.
  fn aux_already_in(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                          target_addr: Addr,
                          target_sp: List‹KExpr›) -> G {
    match load(flat) {
      ListNode.Nil => 0,
      ListNode.Cons(m, rest) =>
        match m {
          (addr, is_aux, sp, _ou) =>
            match is_aux {
              1 =>
                match address_eq(addr, target_addr) {
                  1 =>
                    match spec_params_ptr_eq(sp, target_sp) {
                      1 => 1,
                      _ => aux_already_in(rest, target_addr, target_sp),
                    },
                  _ => aux_already_in(rest, target_addr, target_sp),
                },
              _ => aux_already_in(rest, target_addr, target_sp),
            },
        },
    }
  }

  -- Structural equality on KExpr. Pointer equality is a fast path with
  -- this walk as the complete fallback, so a de-interned duplicate costs
  -- a traversal rather than a wrong answer. Addresses inside `Const` and
  -- `Proj` compare with `address_eq` for the same reason.
  --
  -- Deliberately does NOT whnf: callers compare spine-arg prefixes
  -- against flat-member spec_params, both produced by the same
  -- block-flattening pass, so they are directly comparable.
  fn kexpr_struct_eq(a: KExpr, b: KExpr) -> G {
    match ptr_val(a) - ptr_val(b) {
      0 => 1,
      _ =>
        match load(a) {
          KExprNode.BVar(ia) =>
            match load(b) {
              KExprNode.BVar(ib) =>
                match ia - ib { 0 => 1, _ => 0, },
              _ => 0,
            },
          KExprNode.Srt(la) =>
            match load(b) {
              KExprNode.Srt(lb) => level_struct_eq(la, lb),
              _ => 0,
            },
          KExprNode.Const(ca, lsa) =>
            match load(b) {
              KExprNode.Const(cb, lsb) =>
                match address_eq(ca, cb) {
                  1 => level_list_struct_eq(lsa, lsb),
                  _ => 0,
                },
              _ => 0,
            },
          KExprNode.App(fa, aa) =>
            match load(b) {
              KExprNode.App(fb, ab) =>
                match kexpr_struct_eq(fa, fb) {
                  1 => kexpr_struct_eq(aa, ab),
                  _ => 0,
                },
              _ => 0,
            },
          KExprNode.Lam(ta, ba) =>
            match load(b) {
              KExprNode.Lam(tb, bb) =>
                match kexpr_struct_eq(ta, tb) {
                  1 => kexpr_struct_eq(ba, bb),
                  _ => 0,
                },
              _ => 0,
            },
          KExprNode.Forall(da, xa) =>
            match load(b) {
              KExprNode.Forall(db, xb) =>
                match kexpr_struct_eq(da, db) {
                  1 => kexpr_struct_eq(xa, xb),
                  _ => 0,
                },
              _ => 0,
            },
          KExprNode.Let(ta, va, ba) =>
            match load(b) {
              KExprNode.Let(tb, vb, bb) =>
                match kexpr_struct_eq(ta, tb) {
                  1 =>
                    match kexpr_struct_eq(va, vb) {
                      1 => kexpr_struct_eq(ba, bb),
                      _ => 0,
                    },
                  _ => 0,
                },
              _ => 0,
            },
          KExprNode.Lit(la) =>
            match load(b) {
              KExprNode.Lit(lb) => literal_eq(la, lb),
              _ => 0,
            },
          KExprNode.Proj(sa, fa2, ea) =>
            match load(b) {
              KExprNode.Proj(sb, fb2, eb) =>
                match address_eq(sa, sb) {
                  1 =>
                    match fa2 - fb2 {
                      0 => kexpr_struct_eq(ea, eb),
                      _ => 0,
                    },
                  _ => 0,
                },
              _ => 0,
            },
        },
    }
  }

  fn level_list_struct_eq(a: List‹KLevel›, b: List‹KLevel›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(x, xr) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(y, yr) =>
            match level_struct_eq(x, y) {
              1 => level_list_struct_eq(xr, yr),
              _ => 0,
            },
        },
    }
  }

  -- FAIL-OPEN consumer (`flat_find_pos_kind`): a wrong "not equal" makes
  -- a flat position fail to match, changing the reconstruction. Structural
  -- compare, not raw pointer equality.
  fn spec_params_ptr_eq(a: List‹KExpr›, b: List‹KExpr›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(x, xr) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(y, yr) =>
            match kexpr_struct_eq(x, y) {
              1 => spec_params_ptr_eq(xr, yr),
              _ => 0,
            },
        },
    }
  }

  fn aux_from_recrs_walk(all_members: List‹MutConst›,
                              cur: List‹MutConst›, block_addr: Addr,
                              univ_offset: G,
                              acc: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                              pos: G)
                              -> List‹(Addr, G, List‹KExpr›, List‹KLevel›)› {
    match load(cur) {
      ListNode.Nil => acc,
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Recr(_) =>
            let rec_wrapper = projection_addr(all_members, block_addr, pos);
            let rec_ci = load(get_ci(rec_wrapper));
            let entry_opt = match rec_ci {
              KConstantInfo.Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) =>
                let parent_addr = rec_to_parent_addr(ty, np, nmot, nmin, ni);
                let parent_ci = load(get_ci(parent_addr));
                match parent_ci {
                  KConstantInfo.Induct(pnlvls, _, pnp, _, _, _, pblock, _) =>
                    match address_eq(pblock, block_addr) {
                      1 => (0, parent_addr, 0, pnp, pnlvls),
                      _ => (1, parent_addr, 1, pnp, pnlvls),
                    },
                  _ => (0, parent_addr, 0, 0, 0),
                },
              _ => (0, block_addr, 0, 0, 0),
            };
            match entry_opt {
              (0, _, _, _, _) =>
                aux_from_recrs_walk(all_members, rest, block_addr,
                  univ_offset, acc, pos + 1),
              (_, parent_addr, _, pnp, pnlvls) =>
                let spec_params = extract_aux_spec_params_from_rec(
                  rec_ci, pnp);
                let occ = build_param_lvls_range(univ_offset, pnlvls, 0);
                match aux_already_in(acc, parent_addr, spec_params) {
                  1 =>
                    aux_from_recrs_walk(all_members, rest, block_addr,
                      univ_offset, acc, pos + 1),
                  _ =>
                    let new_acc = list_snoc(acc,
                      (parent_addr, 1, spec_params, occ));
                    aux_from_recrs_walk(all_members, rest, block_addr,
                      univ_offset, new_acc, pos + 1),
                },
            },
          _ =>
            aux_from_recrs_walk(all_members, rest, block_addr,
              univ_offset, acc, pos + 1),
        },
    }
  }

  fn extract_aux_spec_params_from_rec(rec_ci: KConstantInfo,
                                           ext_np: G) -> List‹KExpr› {
    match rec_ci {
      KConstantInfo.Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) =>
        extract_aux_spec_params(ty, np, nmot, nmin, ni, ext_np),
      _ => store(ListNode.Nil),
    }
  }

  -- Combine originals + auxes into full flat block.
  -- Originals come from PARENT inductive block (Muts of Indc members, or
  -- standalone Ind); auxes come from recursor block's Recr members whose
  -- parent inductive is NOT in that primary parent block.
  -- Standalone recursor (rec_block not Muts): return empty flat — canonical
  -- runs only when rec_block is Muts (mutual/aux recursor). Handles solo
  -- recursors with nested-forall recursive fields whose IH construction
  -- would require deeper machinery than currently ported.
  -- The block whose inductives OWN this recursor block, i.e. the one whose
  -- ctors Lean numbers first when laying out minor premises.
  --
  -- It is neither `rec_block_addr` (which in the common layout holds only
  -- `Recr` members) nor `parent_block_addr` (which for an AUX recursor is
  -- the external nested inductive's block). Derive it instead: take the
  -- FIRST `Recr` member of the recursor block and follow it to its
  -- parent's block. For `Tree`'s recursor block that member is `Tree.rec`,
  -- giving `Tree`'s block, which keeps the aux over `List Tree` off flat
  -- position 0 — position 0 must be the primary original. For a mutual
  -- block like `Even`/`Odd` the first recursor's parent is already in the
  -- inductive block, so this agrees with `parent_block_addr` there.
  fn primary_parent_block_of(rec_block_addr: Addr, fallback: Addr) -> Addr {
    let block_c = load_verified_constant(rec_block_addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            first_recr_parent_block(members, members, rec_block_addr, 0,
              fallback),
          _ => fallback,
        },
    }
  }

  fn first_recr_parent_block(all_members: List‹MutConst›,
                                  cur: List‹MutConst›, block_addr: Addr,
                                  pos: G, fallback: Addr) -> Addr {
    match load(cur) {
      ListNode.Nil => fallback,
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Recr(_) =>
            let wrapper = projection_addr(all_members, block_addr, pos);
            let rec_ci = load(get_ci(wrapper));
            match rec_ci {
              KConstantInfo.Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) =>
                let parent = rec_to_parent_addr(ty, np, nmot, nmin, ni);
                let parent_ci = load(get_ci(parent));
                match parent_ci {
                  KConstantInfo.Induct(_, _, _, _, _, _, pb, _) => pb,
                  _ => fallback,
                },
              _ => fallback,
            },
          _ => first_recr_parent_block(all_members, rest, block_addr,
                 pos + 1, fallback),
        },
    }
  }

  fn build_flat_block(rec_block_addr: Addr, parent_block_addr: Addr,
                             univ_offset: G)
                            -> List‹(Addr, G, List‹KExpr›, List‹KLevel›)› {
    -- `build_flat_originals` already handles a standalone parent (single
    -- entry keyed by its own addr). The only thing a non-Muts recursor
    -- block lacks is Recr MEMBERS to scan for nested-aux entries, so skip
    -- that pass — never return an empty flat block. An empty one makes
    -- `flat_find_pos_kind` fail for every solo inductive, which silently
    -- skips the entire canonical rules comparison.
    --
    -- Originals come from the OWNING inductive block (see
    -- `primary_parent_block_of`), not from `parent_block_addr`: for an aux
    -- recursor the parent is the external nested inductive, and seeding
    -- originals from it would put that member at flat position 0. Position
    -- 0 must be the primary, because `ctors_before_pos` derives minor
    -- offsets from flat order and Lean numbers the owning block's ctors
    -- first — get this wrong and the reconstructed rhs references the wrong
    -- minor premise.
    let primary_block = @primary_parent_block_of(rec_block_addr,
      parent_block_addr);
    let originals = @build_flat_originals(primary_block, univ_offset);
    match is_muts_block(rec_block_addr) {
      0 => originals,
      _ =>
        detect_aux_from_recrs_ex(rec_block_addr, primary_block,
                                       univ_offset, originals),
    }
  }

  -- Aux detection variant: parent's block must match parent_block_addr
  -- to be an original (filtered out); otherwise it becomes an aux.
  fn detect_aux_from_recrs_ex(rec_block_addr: Addr,
                                    parent_block_addr: Addr,
                                    univ_offset: G,
                                    originals: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›)
                                   -> List‹(Addr, G, List‹KExpr›, List‹KLevel›)› {
    let block_c = load_verified_constant(rec_block_addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            aux_from_recrs_walk_ex(members, members, rec_block_addr,
                                        parent_block_addr, univ_offset,
                                        originals, 0),
          _ => originals,
        },
    }
  }

  fn aux_from_recrs_walk_ex(all_members: List‹MutConst›,
                                  cur: List‹MutConst›,
                                  rec_block_addr: Addr,
                                  primary_parent_block: Addr,
                                  univ_offset: G,
                                  acc: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                                  pos: G)
                                 -> List‹(Addr, G, List‹KExpr›, List‹KLevel›)› {
    match load(cur) {
      ListNode.Nil => acc,
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Recr(_) =>
            let rec_wrapper = projection_addr(all_members, rec_block_addr, pos);
            let rec_ci = load(get_ci(rec_wrapper));
            let entry_opt = match rec_ci {
              KConstantInfo.Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) =>
                let parent_addr = rec_to_parent_addr(ty, np, nmot, nmin, ni);
                let parent_ci = load(get_ci(parent_addr));
                match parent_ci {
                  KConstantInfo.Induct(pnlvls, _, pnp, _, _, _, pblock, _) =>
                    match address_eq(pblock, primary_parent_block) {
                      1 => (0, parent_addr, 0, pnp, pnlvls),
                      _ => (1, parent_addr, 1, pnp, pnlvls),
                    },
                  _ => (0, parent_addr, 0, 0, 0),
                },
              _ => (0, primary_parent_block, 0, 0, 0),
            };
            match entry_opt {
              (0, _, _, _, _) =>
                aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
                  primary_parent_block, univ_offset, acc, pos + 1),
              (_, parent_addr, _, pnp, pnlvls) =>
                let spec_params = extract_aux_spec_params_from_rec(
                  rec_ci, pnp);
                let occ = extract_aux_occ_us(rec_ci);
                match aux_already_in(acc, parent_addr, spec_params) {
                  1 =>
                    aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
                      primary_parent_block, univ_offset, acc, pos + 1),
                  _ =>
                    let new_acc = list_snoc(acc,
                      (parent_addr, 1, spec_params, occ));
                    aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
                      primary_parent_block, univ_offset, new_acc, pos + 1),
                },
            },
          _ =>
            aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
              primary_parent_block, univ_offset, acc, pos + 1),
        },
    }
  }

  -- Look up flat member position by target inductive addr. Returns
  -- (found=0/1, pos). For non-aux target: matches original's member_addr.
  -- For aux target: matches aux's target ext addr.
  fn flat_find_pos(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                        target_addr: Addr, pos: G) -> (G, G) {
    match load(flat) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(m, rest) =>
        match m {
          (member_addr, _is_aux, _sp, _ou) =>
            match address_eq(member_addr, target_addr) {
              1 => (1, pos),
              _ => flat_find_pos(rest, target_addr, pos + 1),
            },
        },
    }
  }

  -- Aux-aware lookup: prefer aux entry with matching (addr, spec_params)
  -- if want_aux=1, else prefer original (is_aux=0) match by addr.
  fn flat_find_pos_kind(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                             target_addr: Addr,
                             want_aux: G,
                             want_sp: List‹KExpr›,
                             pos: G) -> (G, G) {
    match load(flat) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(m, rest) =>
        match m {
          (member_addr, is_aux, sp, _ou) =>
            let addr_match = address_eq(member_addr, target_addr);
            let kind_eq = match want_aux - is_aux {
              0 => 1,
              _ => 0,
            };
            let sp_eq = match want_aux {
              1 => spec_params_ptr_eq(sp, want_sp),
              _ => 1,
            };
            match (addr_match * kind_eq) * sp_eq {
              1 => (1, pos),
              _ => flat_find_pos_kind(rest, target_addr, want_aux,
                                           want_sp, pos + 1),
            },
        },
    }
  }

  -- Get member at position (returns (addr, is_aux, spec_params, occ_us)).
  fn flat_member_at(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                         pos: G) -> (Addr, G, List‹KExpr›, List‹KLevel›) {
    match load(flat) {
      ListNode.Nil => (store([0u8; 32]), 0, store(ListNode.Nil),
                       store(ListNode.Nil)),
      ListNode.Cons(m, rest) =>
        match pos {
          0 => m,
          _ => flat_member_at(rest, pos - 1),
        },
    }
  }

  -- ============================================================================
  -- Motive type construction.
  -- Motive: `∀ (indices) (major : Ind occ_us subst_params indices), Sort elim`.
  -- For non-aux: subst_params = recursor's param BVars.
  -- For aux: subst_params = spec_params (lifted).
  -- ============================================================================

  fn subst_param_for(j: G, n_rec_params: G, is_aux: G,
                          spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => store(KExprNode.BVar((n_rec_params - 1) - j)),
      _ =>
        let len = list_length(spec_params);
        match u32_less_than(j, len) {
          1 => list_lookup(spec_params, j),
          _ => store(KExprNode.BVar((n_rec_params - 1) - j)),
        },
    }
  }

  -- Peel n Foralls; for each binder j substitute per is_aux:
  -- non-aux: BVar(n_rec_params - 1 - j).
  -- aux: spec_params[j] when j < |spec_params|, else BVar(n_rec_params - 1 - j).
  fn peel_motive_params_subst(ty: KExpr, n: G, n_rec_params: G,
                                    is_aux: G, spec_params: List‹KExpr›,
                                    j: G) -> KExpr {
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

  -- Mirror crates/kernel/src/inductive.rs (build_motive_type_flat, the
  -- `for _ in 0..n_indices { whnf; All => push; _ => break }` loop):
  -- whnf before each peel, stop tolerantly when no binder remains.
  -- Index binders can hide under definitional wrappers (e.g. a result type
  -- `Set σ` only exposes its `σ → Prop` index binder after whnf), and
  -- without the whnf the match falls through on the `App` node — an
  -- abort that wrongly rejected every inductive whose declared type is a
  -- wrapper (mathlib's CategoryTheory.MorphismProperty.ofHoms and ~30
  -- siblings; minimized as the `HiddenIdx`/`PredOver` fixture).
  --
  -- Structural first, whnf only on the fallback: `whnf` of a `Forall` is
  -- that `Forall`, so the two orders agree, and the common case pays no
  -- reduction. The empty context mirrors the reference, which performs
  -- this walk with no ctx pushes ("No ctx push" there); the type's loose
  -- BVars are recursor-param references that stay stuck either way, and a
  -- context-poorer whnf can only under-reduce, never invent a reduction.
  --
  -- The tolerant stop cannot be exploited to accept a short index
  -- telescope: `get_result_sort_level` already peels exactly
  -- n_params + n_indices Foralls off the same declared type INTOLERANTLY
  -- (and whnf'd) before any of this runs, so reaching here with fewer
  -- binders than `n` is impossible for a block that passed validation.
  fn collect_index_doms(ty: KExpr, n: G) -> List‹KExpr› {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            store(ListNode.Cons(dom, collect_index_doms(body, n - 1))),
          _ =>
            match load(whnf(ty, store(ListNode.Nil))) {
              KExprNode.Forall(dom, body) =>
                store(ListNode.Cons(dom, collect_index_doms(body, n - 1))),
              _ => store(ListNode.Nil),
            },
        },
    }
  }

  -- Apply recursor param BVars: head applied to BVar(n_rec_params-1+depth),
  -- BVar(n_rec_params-2+depth), ..., BVar(depth) (in that order —
  -- outermost recursor-param first).
  fn build_major_params(head: KExpr, n_rec_params: G, depth: G,
                             i: G) -> KExpr {
    match n_rec_params - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(((n_rec_params - 1) - i) + depth));
        build_major_params(store(KExprNode.App(head, v)),
          n_rec_params, depth, i + 1),
    }
  }

  fn apply_spec_params_lifted(head: KExpr, spec_params: List‹KExpr›,
                                    depth: G) -> KExpr {
    match load(spec_params) {
      ListNode.Nil => head,
      ListNode.Cons(sp, rest) =>
        let lifted = expr_lift(sp, depth, 0);
        apply_spec_params_lifted(store(KExprNode.App(head, lifted)),
          rest, depth),
    }
  }

  -- For aux: apply spec_params (each lifted by depth=n_indices) to head.
  -- For non-aux: apply n_rec_params recursor-param BVars to head.
  fn build_major_args_for_member(head: KExpr, n_rec_params: G,
                                       depth: G, is_aux: G,
                                       spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => build_major_params(head, n_rec_params, depth, 0),
      _ => apply_spec_params_lifted(head, spec_params, depth),
    }
  }

  -- Apply index BVars: head applied to BVar(n_indices-1-i) for
  -- i in 0..n_indices (outermost index first).
  fn build_major_indices(head: KExpr, n_indices: G, i: G) -> KExpr {
    match n_indices - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar((n_indices - 1) - i));
        build_major_indices(store(KExprNode.App(head, v)),
          n_indices, i + 1),
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

  -- Collect the first `n` Forall domains, reducing at every step so a
  -- binder hidden behind a definitional wrapper is still found. Intolerant:
  -- running out of Foralls means the declared arity disagrees with the
  -- inductive's, which must reject rather than silently produce a shorter
  -- telescope for the reconstruction to be compared against.
  fn collect_n_doms_whnf(ty: KExpr, n: G) -> (List‹KExpr›, KExpr) {
    match n {
      0 => (store(ListNode.Nil), ty),
      _ =>
        -- Structural first, reduce only if that fails. These bodies carry
        -- loose BVars (the walk substitutes nothing and the context is
        -- empty), and reducing such a term unconditionally can destroy a
        -- Forall that was already in plain sight — which silently shortens
        -- the telescope the reconstruction is built from.
        match load(ty) {
          KExprNode.Forall(dom, body) =>
            match collect_n_doms_whnf(body, n - 1) {
              (rest, after) => (store(ListNode.Cons(dom, rest)), after),
            },
          _ =>
            match load(whnf(ty, store(ListNode.Nil))) {
              KExprNode.Forall(dom, body) =>
                match collect_n_doms_whnf(body, n - 1) {
                  (rest, after) => (store(ListNode.Cons(dom, rest)), after),
                },
              -- Tolerant, matching both reference kernels: stop early rather
              -- than reject here. A short telescope yields a reconstruction
              -- that differs from the declared type, so the def-eq assert
              -- still rejects — with an accurate message instead of this one.
              _ => (store(ListNode.Nil), ty),
            },
        },
    }
  }

  -- Index domains sit inside the motive and minor binders in the recursor
  -- telescope, so each must be lifted past them. Position `i` is already
  -- under the `i` index binders that precede it, hence the `i` cutoff.
  fn list_lift_indices(doms: List‹KExpr›, shift: G, i: G) -> List‹KExpr› {
    match load(doms) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(d, rest) =>
        store(ListNode.Cons(expr_lift(d, shift, i),
                            list_lift_indices(rest, shift, i + 1))),
    }
  }

  -- Apply the recursor's own parameters to the major premise's head. For an
  -- aux member the parameters are the stored spec_params (lifted from the
  -- recursor-param frame to this depth) rather than the param BVars.
  fn build_major_args_for_self(head: KExpr, n_rec_params: G,
                                     top_bvar: G, spec_lift: G,
                                     is_aux: G,
                                     spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      1 => apply_spec_params_lifted(head, spec_params, spec_lift),
      _ => build_apply_bvars_decreasing(head, n_rec_params, top_bvar, 0),
    }
  }

  -- The conclusion applies the motive to the index binders, then to the
  -- major premise: `motive i_0 ... i_{n-1} major`. Index binder `j` sits at
  -- BVar(n_indices - j) once the major binder is in scope.
  fn apply_indices_in_conclusion(head: KExpr, n_indices: G, i: G) -> KExpr {
    match n_indices - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(n_indices - i));
        apply_indices_in_conclusion(store(KExprNode.App(head, v)),
          n_indices, i + 1),
    }
  }

  -- Full motive type sig for one flat member.
  fn build_motive_type_flat(member_addr: Addr, ind_ty: KExpr,
                                  n_own_params: G, n_indices: G,
                                  occurrence_us: List‹KLevel›,
                                  elim_level: KLevel,
                                  n_rec_params: G,
                                  is_aux: G,
                                  spec_params: List‹KExpr›) -> KExpr {
    let ind_ty_inst = expr_inst_levels(ind_ty, occurrence_us);
    let after_params = peel_motive_params_subst(ind_ty_inst, n_own_params,
      n_rec_params, is_aux, spec_params, 0);
    let index_doms = collect_index_doms(after_params, n_indices);
    let head = store(KExprNode.Const(member_addr, occurrence_us));
    let with_args = @build_major_args_for_member(head, n_rec_params,
      n_indices, is_aux, spec_params);
    let major_ty = build_major_indices(with_args, n_indices, 0);
    let sort_e = store(KExprNode.Srt(elim_level));
    let with_major = store(KExprNode.Forall(major_ty, sort_e));
    wrap_foralls(with_major, index_doms)
  }

  -- Build all motive types for a flat block. Each member's motive is
  -- lifted by its position j in the flat list (later motives are under
  -- more binders in the recursor's outer Lam sequence).
  fn build_all_motives(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                            elim_level: KLevel, n_rec_params: G)
                            -> List‹KExpr› {
    build_all_motives_walk(flat, elim_level, n_rec_params, 0)
  }

  -- Apply head to motive BVars starting at `start` descending.
  fn build_motive_apps(head: KExpr, n_motives: G, start: G,
                             i: G) -> KExpr {
    match n_motives - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - i));
        build_motive_apps(store(KExprNode.App(head, v)), n_motives,
          start, i + 1),
    }
  }

  fn build_minor_apps(head: KExpr, n_minors: G, start: G,
                            i: G) -> KExpr {
    match n_minors - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - i));
        build_minor_apps(store(KExprNode.App(head, v)), n_minors,
          start, i + 1),
    }
  }

  -- Wrap body in Lams outside-in: doms = [d0, d1, ..., dM] →
  -- `Lam d0. Lam d1. ... Lam dM. body`.
  fn wrap_lams(body: KExpr, doms: List‹KExpr›) -> KExpr {
    match load(doms) {
      ListNode.Nil => body,
      ListNode.Cons(dom, rest) =>
        store(KExprNode.Lam(dom, wrap_lams(body, rest))),
    }
  }

  -- Full canonical rules identity check (aux port final assembly).
  -- Uses complete reference-parallel pipeline: build_flat_block →
  -- build_peer_recs → build_flat_own_params → populate_rules →
  -- compare_rules. Handles solo, mutual, and aux recursors.
  --
  -- This is the check that makes a recursor's rules trustworthy: without
  -- it, neither a recursor's type nor its rules are validated against a
  -- reconstruction, and `is_aux` alone decides how much checking happens.
  -- Called from check_recursor_member for every recursor.
  -- Reconstruct a recursor's canonical type from the inductive it
  -- eliminates:
  --
  --   forall (params) (motives) (minors) (indices) (major), motive_self indices major
  --
  -- The declared type is adversary-supplied in full — every numeric field
  -- and the type itself come from the Ixon record — so without comparing
  -- against this reconstruction a recursor may claim any conclusion at all,
  -- `False` included, while its rules still reconstruct correctly.
  fn build_rec_type(ind_ty: KExpr, ind_nlvls: G, n_params: G, n_indices: G,
                          elim_level: KLevel, univ_offset: G,
                          flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                          flat_own_params: List‹G›, self_pos: G) -> KExpr {
    -- Walk the params over the PRIMARY inductive (flat position 0), not the
    -- recursor's parent. For an aux recursor the parent is the external
    -- inductive being nested into (e.g. `Array`, one param) while n_params
    -- is the block's own param count, so peeling the parent's type runs off
    -- the end and yields a short, malformed telescope.
    match flat_member_at(flat, 0) {
      (prim_addr, _pia, _pisp, _piou) =>
        match load(get_ci(prim_addr)) {
          KConstantInfo.Induct(prim_nlvls, prim_ty, _, _, _, _, _, _) =>
            build_rec_type_from(prim_ty, prim_nlvls, ind_ty, ind_nlvls,
              n_params, n_indices, elim_level, univ_offset, flat,
              flat_own_params, self_pos),
          _ =>
            build_rec_type_from(ind_ty, ind_nlvls, ind_ty, ind_nlvls,
              n_params, n_indices, elim_level, univ_offset, flat,
              flat_own_params, self_pos),
        },
    }
  }

  fn build_rec_type_from(prim_ty: KExpr, prim_nlvls: G,
                               ind_ty: KExpr, ind_nlvls: G,
                               n_params: G, n_indices: G,
                               elim_level: KLevel, univ_offset: G,
                               flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                               flat_own_params: List‹G›, self_pos: G) -> KExpr {
    let n_motives = list_length(flat);
    let motive_base = n_params;
    -- The params telescope is read under the same universe shift the flat
    -- block was built with, so the reconstructed binders carry the levels
    -- the declared type must.
    let p_us = build_param_lvls_range(univ_offset, prim_nlvls, 0);
    match collect_n_doms_whnf(expr_inst_levels(prim_ty, p_us), n_params) {
      (param_doms, after_params) =>
        let motive_doms = build_all_motives(flat, elim_level, n_params);
        let minor_doms = build_all_minors(flat, flat_own_params, n_params,
          n_motives, motive_base);
        let n_minors = list_length(minor_doms);
        let (self_addr, self_is_aux, self_spec_params, self_occ_us) =
          flat_member_at(flat, self_pos);
        -- The index binders come from the SELF member's inductive
        -- type, NOT the primary's `after_params`: mutual members may
        -- carry distinct index telescopes (mathlib's
        -- `Lists.Equiv : Lists α → Lists α → Prop`, mutual with
        -- `Lists'.Subset : Lists' α true → Lists' α true → Prop`),
        -- and reading member 0's indices for every member rejected
        -- the block's second recursor. Same peel/subst conventions
        -- as the motives (`build_motive_type_flat`), same
        -- occurrence-universe instantiation as the reference
        -- (`inductive.rs build_rec_type`, "Indices for THIS
        -- inductive").
        let KConstantInfo.Induct(_, self_ind_ty, self_own_params,
          _, _, _, _, _) = load(get_ci(self_addr));
        let self_ty_inst = expr_inst_levels(self_ind_ty, self_occ_us);
        let self_after_params = peel_motive_params_subst(self_ty_inst,
          self_own_params, n_params, self_is_aux, self_spec_params, 0);
        let index_doms_raw = collect_index_doms(self_after_params,
          n_indices);
        let index_doms = list_lift_indices(index_doms_raw,
          n_motives + n_minors, 0);
        let head = store(KExprNode.Const(self_addr, self_occ_us));
        let pre_major_depth = ((n_params + n_motives) + n_minors) + n_indices;
        let with_args = @build_major_args_for_self(head, n_params,
          pre_major_depth - 1, (n_motives + n_minors) + n_indices,
          self_is_aux, self_spec_params);
        let major_ty = build_major_indices(with_args, n_indices, 0);
        -- Conclusion is built with the major binder in scope, hence the
        -- +1: motive_self applied to the index binders, then the major.
        let depth_after_major = pre_major_depth + 1;
        let motive_var = (depth_after_major - 1) - (motive_base + self_pos);
        let motive_ref = store(KExprNode.BVar(motive_var));
        let with_indices = apply_indices_in_conclusion(motive_ref,
          n_indices, 0);
        let conclusion = store(KExprNode.App(with_indices,
          store(KExprNode.BVar(0))));
        let with_major = store(KExprNode.Forall(major_ty, conclusion));
        let with_idx_foralls = wrap_foralls(with_major, index_doms);
        let with_minors = wrap_foralls(with_idx_foralls, minor_doms);
        let with_motives = wrap_foralls(with_minors, motive_doms);
        wrap_foralls(with_motives, param_doms),
    }
  }

  fn check_recursor_canonical_full(rec_ci: KConstantInfo, addr: Addr,
                                          parent_ci: KConstantInfo,
                                          parent_addr: Addr) {
    match rec_ci {
      KConstantInfo.Rec(nlvls, ty, n_p, n_i, n_mot, n_min, rules,
                          _k_flag, _uns, rec_block_addr, _rec_idx) =>
        match parent_ci {
          KConstantInfo.Induct(pnlvls, pty, pnp, pni, num_ctors, _,
                                 parent_block_addr, parent_ind_idx) =>
            let single_ctor_pair = match num_ctors {
              1 =>
                let cci = load(get_ci_cprj(parent_block_addr,
                  parent_ind_idx, 0));
                (1, cci),
              _ =>
                (0, KConstantInfo.Axiom(0, store(KExprNode.Srt(
                  store(KLevelNode.Zero))), 0)),
            };
            let result_level = get_result_sort_level(pty, pnp + pni,
              store(ListNode.Nil));
            let univ_offset = is_large_eliminator(result_level,
              num_ctors, single_ctor_pair,
              ind_is_solo(parent_block_addr, parent_addr));
            let elim_level = match univ_offset {
              1 => store(KLevelNode.Param(0)),
              _ => store(KLevelNode.Zero),
            };
            let rec_lvls_list = build_rec_lvls_list(nlvls, 0);
            let flat = build_flat_block(rec_block_addr, parent_block_addr,
                                              univ_offset);
            let peer_recs = build_peer_recs(flat, rec_block_addr, addr);
            let flat_own_params = build_flat_own_params(flat);
            let rec_is_aux = is_muts_block(rec_block_addr) *
              is_muts_block(parent_block_addr) *
              (1 - address_eq(rec_block_addr, parent_block_addr));
            let rec_spec_params = match rec_is_aux {
              1 => extract_aux_spec_params_from_rec(rec_ci, pnp),
              _ => store(ListNode.Nil),
            };
            -- Locate this recursor's parent in the flat block.
            --
            -- The kind-aware lookup disambiguates the case where one
            -- address appears both as an original and as a nested-aux
            -- entry with distinct spec_params. It is a REFINEMENT, not a
            -- gate: on a miss, fall back to an address-only match and let
            -- the entry supply is_aux/spec_params below, which is what
            -- `flat_member_at` already reads.
            --
            -- Requiring the caller's computed `rec_is_aux` to match was a
            -- silent skip of the whole canonical rules comparison —
            -- measured at 132 of the suite's recursor checks, every one
            -- with `want_aux = 1` against a flat list of `is_aux = 0`
            -- originals. A recursor living in a different block from its
            -- inductives is not the same thing as an aux recursor, but
            -- `rec_is_aux` is computed from exactly that block
            -- difference. A parent genuinely absent from the flat block
            -- is a real inconsistency and now fails hard.
            let kind_hit = flat_find_pos_kind(flat, parent_addr,
                                                    rec_is_aux,
                                                    rec_spec_params, 0);
            match kind_hit {
              (1, self_pos) =>
                canonical_rules_at_pos(flat, self_pos, num_ctors,
                  parent_block_addr, parent_ind_idx, n_p, n_mot, n_min,
                  rec_lvls_list, peer_recs, flat_own_params, rules,
                  ty, pty, pnlvls, pni, elim_level, univ_offset),
              _ =>
                match flat_find_pos(flat, parent_addr, 0) {
                  (1, self_pos) =>
                    canonical_rules_at_pos(flat, self_pos, num_ctors,
                      parent_block_addr, parent_ind_idx, n_p, n_mot,
                      n_min, rec_lvls_list, peer_recs, flat_own_params,
                      rules, ty, pty, pnlvls, pni, elim_level, univ_offset),
                },
            },
          _ => (),
        },
    }
  }

  -- Reconstruct the canonical rules for the flat member at `self_pos`
  -- and compare them against the recursor's stored rules. Split out of
  -- `check_recursor_canonical_full` so both the kind-aware lookup and the
  -- address-only fallback can tail-call it (this compiler rejects a
  -- non-tail `match` bound by `let`).
  fn canonical_rules_at_pos(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                                 self_pos: G, num_ctors: G,
                                 parent_block_addr: Addr,
                                 parent_ind_idx: G, n_p: G, n_mot: G,
                                 n_min: G, rec_lvls_list: List‹KLevel›,
                                 peer_recs: List‹Addr›,
                                 flat_own_params: List‹G›,
                                 rules: List‹KRecRule›,
                                 ty: KExpr, pty: KExpr, pnlvls: G, pni: G,
                                 elim_level: KLevel, univ_offset: G) {
    match flat_member_at(flat, self_pos) {
      (_, is_aux, spec_params, occ_us) =>
        -- Validate the DECLARED type against the reconstruction. The rule
        -- comparison below covers only rule right-hand sides; on its own it
        -- leaves the motive premises, the minor premises, the index binders
        -- and the CONCLUSION unconstrained, which is enough for a recursor
        -- to declare `... -> False` and still reconstruct every rule
        -- correctly. Both the kind-aware lookup and the address-only
        -- fallback route through here, so neither can skip this.
        let canonical_ty = build_rec_type(pty, pnlvls, n_p, pni, elim_level,
          univ_offset, flat, flat_own_params, self_pos);
        assert_eq!(k_is_def_eq(ty, canonical_ty, store(ListNode.Nil)), 1,
          "recursor's declared type is not def-eq to the canonical reconstruction");
        let self_ctors_offset = ctors_before_pos(flat, self_pos, 0);
        let canonical = populate_rules(num_ctors, self_ctors_offset,
          parent_block_addr, parent_ind_idx, n_p, n_mot, n_min, occ_us,
          rec_lvls_list, flat, peer_recs, flat_own_params, is_aux,
          spec_params, 0);
        compare_rules(rules, canonical, n_p, n_mot, n_min,
          parent_block_addr, parent_ind_idx, num_ctors, 0),
    }
  }

  -- Sum of num_ctors for flat members before target_pos.
  fn ctors_before_pos(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                            target_pos: G, cur_pos: G) -> G {
    match cur_pos - target_pos {
      0 => 0,
      _ =>
        match load(flat) {
          ListNode.Nil => 0,
          ListNode.Cons(m, rest) =>
            match m {
              (addr, _, _, _) =>
                let ci = load(get_ci(addr));
                let n = match ci {
                  KConstantInfo.Induct(_, _, _, _, nc, _, _, _) => nc,
                  _ => 0,
                };
                n + ctors_before_pos(rest, target_pos, cur_pos + 1),
            },
        },
    }
  }

  -- Populate canonical rhs bodies for one recursor's rules (self's
  -- ctors only). ctor_minor_index = ctors_before_self + cidx.
  fn populate_rules(num_ctors: G, self_ctors_offset: G,
                          block_addr: Addr, ind_idx: G,
                          n_params: G, n_motives: G, n_minors: G,
                          occurrence_us: List‹KLevel›,
                          rec_lvls_list: List‹KLevel›,
                          flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                          peer_recs: List‹Addr›,
                          flat_own_params: List‹G›,
                          is_aux: G, spec_params: List‹KExpr›,
                          cidx: G) -> List‹KExpr› {
    match num_ctors - cidx {
      0 => store(ListNode.Nil),
      _ =>
        let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, cidx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, _, np, _, _) =>
            let ctor_minor_index = self_ctors_offset + cidx;
            let rhs = build_rule_rhs(ctor_ty, ctor_minor_index,
              n_params, n_motives, n_minors, np, occurrence_us,
              rec_lvls_list, flat, peer_recs, flat_own_params,
              is_aux, spec_params);
            store(ListNode.Cons(rhs,
              populate_rules(num_ctors, self_ctors_offset, block_addr,
                ind_idx, n_params, n_motives, n_minors, occurrence_us,
                rec_lvls_list, flat, peer_recs, flat_own_params, is_aux,
                spec_params, cidx + 1))),
          _ => store(ListNode.Nil),
        },
    }
  }

  -- Compare stored rules against canonical rhs list. Per rule: peel
  -- (n_p + n_mot + n_min + nf) Lams off stored rhs, def_eq against
  -- canonical body.
  fn compare_rules(stored: List‹KRecRule›, canonical: List‹KExpr›,
                        n_p: G, n_mot: G, n_min: G,
                        block_addr: Addr, ind_idx: G, num_ctors: G, pos: G) {
    match load(stored) {
      ListNode.Nil => (),
      ListNode.Cons(r, rest) =>
        match r {
          KRecRule.Mk(cidx, nf, rhs) =>
            -- Pin the rule's own labels against the constructor it claims.
            -- Equivalents of these three live in `check_rec_rules_walk`,
            -- which nothing calls; the live path had none of them.
            --
            -- `cidx` selects the rule at reduction time (`find_rule` in
            -- try_iota) while `compare_rules` pairs stored against
            -- canonical POSITIONALLY, so permuted labels would fire one
            -- constructor's rule for another. It holds today only because
            -- ingress assigns `cidx` positionally (`Convert.lean`) — this
            -- makes it an asserted invariant rather than a coincidence.
            --
            -- `nf` decides how `try_iota` splits the constructor's
            -- arguments (`field_start = ctor_fields_len - rfields`), so a
            -- wrong value hands the minor premise the wrong slice.
            assert_eq!(cidx, pos,
              "recursor rule is out of ctor order");
            assert_eq!(u32_less_than(cidx, num_ctors), 1,
              "recursor rule names a ctor index out of range");
            let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, cidx));
            match ctor_ci {
              KConstantInfo.Ctor(_, _, _, _, _, _, c_nf, _) =>
                assert_eq!(nf, c_nf,
                  "recursor rule field count differs from the ctor's");
                (),
            };
            match load(canonical) {
              ListNode.Nil => (),
              ListNode.Cons(cbody, crest) =>
                let total = ((n_p + n_mot) + n_min) + nf;
                match peel_n_lams_collect(rhs, total, 0,
                        store(ListNode.Nil)) {
                  (stored_body, peeled, _) =>
                    assert_eq!(peeled, total,
                      "recursor rule rhs has too few binders to peel");
                    -- Compare under an EMPTY context, discarding the
                    -- domains just peeled.
                    --
                    -- Those domains come off the STORED rule, so they are
                    -- prover-authored and unvalidated — nothing compares
                    -- them against the canonical reconstruction, and
                    -- reduction never consults them (`try_iota` beta-
                    -- reduces straight through). Feeding them to
                    -- `k_is_def_eq` let the prover choose what the two
                    -- sides INFER to: retype every binder to a Prop and
                    -- proof irrelevance accepts any body, so a recursor
                    -- whose computation rules are swapped between
                    -- constructors passed.
                    --
                    -- An honest rule matches the reconstruction
                    -- structurally, and the structural path never
                    -- consults the context — it compares `BVar i`
                    -- against `BVar i` directly. Anything that instead
                    -- needs to INFER a bound variable's type now runs out
                    -- of context and aborts, which is the safe direction.
                    assert_eq!(k_is_def_eq(stored_body, cbody,
                        store(ListNode.Nil)), 1,
                      "recursor rule rhs differs from canonical reconstruction");
                    (),
                };
                compare_rules(rest, crest, n_p, n_mot, n_min,
                  block_addr, ind_idx, num_ctors, pos + 1),
            },
        },
    }
  }

  -- Full IH construction with peer_recs + flat_own_params + arbitrary
  -- n_motives / n_minors. Mirror apply_ihs (Inductive.lean:1729+).
  fn apply_ihs_full(head: KExpr, rec_indices: List‹G›,
                          rec_member_idxs: List‹G›,
                          field_doms: List‹KExpr›,
                          peer_recs: List‹Addr›,
                          flat_own_params: List‹G›,
                          n_params: G, n_motives: G, n_minors: G,
                          n_fields: G, rec_lvls_list: List‹KLevel›,
                          k: G) -> KExpr {
    match load(rec_indices) {
      ListNode.Nil => head,
      ListNode.Cons(field_idx, rest) =>
        let mem_idx = list_lookup_or_default(rec_member_idxs, k, 0);
        let target_rec = list_lookup_or_default(peer_recs, mem_idx,
          store([0u8; 32]));
        let target_n_params = list_lookup_or_default(flat_own_params,
          mem_idx, 0);
        let body_depth = ((n_params + n_motives) + n_minors) + n_fields;
        let dom = list_lookup(field_doms, field_idx);
        let dom_s1 = expr_lift(dom, n_fields - field_idx, 0);
        let dom_lifted = expr_lift(dom_s1, n_motives + n_minors, n_fields);
        match peel_leading_foralls(dom_lifted) {
          (forall_doms, inner_body) =>
            let n_xs = list_length(forall_doms);
            let inner_depth = body_depth + n_xs;
            let rec_const = store(KExprNode.Const(target_rec, rec_lvls_list));
            let with_params = build_apply_bvars_decreasing(rec_const,
              n_params, inner_depth - 1, 0);
            let with_motives = build_motive_apps(with_params, n_motives,
              (inner_depth - 1) - n_params, 0);
            let with_minors = build_minor_apps(with_motives, n_minors,
              ((inner_depth - 1) - n_params) - n_motives, 0);
            -- Reduce before reading the spine. `is_rec_field` whnf's to
            -- CLASSIFY the field, so a domain like `constType (T a) (T a)`
            -- is correctly seen as recursive — but the index arguments of
            -- the induction hypothesis have to come from the REDUCED head
            -- too. Taking them from the unreduced domain yields the
            -- wrapper's arguments (`drop 1 [A, B] = [B]`) instead of the
            -- inductive's (`drop 1 [a] = []`), so the IH was applied to one
            -- argument too many.
            match collect_spine(whnf(inner_body, store(ListNode.Nil))) {
              (_dh, dargs) =>
                let idx_args = list_drop(dargs, target_n_params);
                let with_idx = apply_spine_expr(with_minors, idx_args);
                let field_base = ((n_fields - 1) - field_idx) + n_xs;
                let field_ref = store(KExprNode.BVar(field_base));
                let field_app = build_apply_xs(field_ref, n_xs, 0);
                let ih_inner = store(KExprNode.App(with_idx, field_app));
                let ih = wrap_lams(ih_inner, forall_doms);
                let new_head = store(KExprNode.App(head, ih));
                apply_ihs_full(new_head, rest, rec_member_idxs,
                  field_doms, peer_recs, flat_own_params, n_params,
                  n_motives, n_minors, n_fields, rec_lvls_list, k + 1),
            },
        },
    }
  }

  -- Full canonical rule rhs BODY (all outer Lams peeled). Mirror
  -- build_rule_rhs (Inductive.lean:1641+). ctor_minor_index = global
  -- minor position (across all flat members' ctors).
  fn build_rule_rhs(ctor_ty: KExpr, ctor_minor_index: G,
                          n_params: G, n_motives: G, n_minors: G,
                          n_own_params: G,
                          occurrence_us: List‹KLevel›,
                          rec_lvls_list: List‹KLevel›,
                          flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                          peer_recs: List‹Addr›,
                          flat_own_params: List‹G›,
                          is_aux: G, spec_params: List‹KExpr›) -> KExpr {
    let ctor_ty_inst = expr_inst_levels(ctor_ty, occurrence_us);
    let after_params_raw = peel_n_foralls(ctor_ty_inst, n_own_params);
    let n_fields = count_foralls_body(after_params_raw, 0);
    let body_depth = ((n_params + n_motives) + n_minors) + n_fields;
    -- Peel into the recursor-param frame, not the final body frame:
    -- apply_ihs_full's two lifts already carry a field domain from the
    -- param frame to the body frame (together they add exactly
    -- body_depth - n_params to anything above the field cutoff).
    -- Substituting body-frame indices here would apply that transport a
    -- second time, leaving every param reference that survives into a
    -- binder domain over-shifted.
    let after_params = peel_ctor_params_subst(ctor_ty_inst, n_own_params,
      n_own_params, 0, is_aux, spec_params, 0);
    -- spec_lift_by must name the same frame the spec_params are stored
    -- in; walk_fields_classify adds the walk depth itself.
    match walk_fields_classify(after_params, flat, store(ListNode.Nil),
            store(ListNode.Nil), store(ListNode.Nil), 0, 0) {
      (field_doms, rec_indices, rec_member_idxs, _ret_ty) =>
        let minor_var = (body_depth - 1) - ((n_params + n_motives) +
                                              ctor_minor_index);
        let base = store(KExprNode.BVar(minor_var));
        let with_fields = build_apply_field_bvars(base, n_fields,
          n_fields, 0);
        apply_ihs_full(with_fields, rec_indices, rec_member_idxs,
          field_doms, peer_recs, flat_own_params, n_params, n_motives,
          n_minors, n_fields, rec_lvls_list, 0),
    }
  }

  -- Build list of peer recursor addrs (one per flat member).
  -- For each flat member, find the Recr in rec_block_addr's Muts whose
  -- parsed parent addr matches AND spec_params match. spec-match
  -- disambiguates auxes with same target but distinct specs (DedupM).
  fn build_peer_recs(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                          rec_block_addr: Addr,
                          rec_self_addr: Addr) -> List‹Addr› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (member_addr, is_aux, sp, _ou) =>
            let peer = find_peer_recursor_with_spec(rec_block_addr,
              member_addr, sp, is_aux, rec_self_addr);
            store(ListNode.Cons(peer,
              build_peer_recs(rest, rec_block_addr, rec_self_addr))),
        },
    }
  }

  fn find_peer_recursor_with_spec(block_addr: Addr,
                                        target_ind_addr: Addr,
                                        target_sp: List‹KExpr›,
                                        target_is_aux: G,
                                        rec_self_addr: Addr) -> Addr {
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            find_peer_rec_spec_walk(members, members, block_addr,
              target_ind_addr, target_sp, target_is_aux, rec_self_addr, 0),
          _ => rec_self_addr,
        },
    }
  }

  fn find_peer_rec_spec_walk(all_members: List‹MutConst›,
                                   cur: List‹MutConst›, block_addr: Addr,
                                   target_ind_addr: Addr,
                                   target_sp: List‹KExpr›,
                                   target_is_aux: G,
                                   rec_self_addr: Addr, pos: G) -> Addr {
    match load(cur) {
      ListNode.Nil => rec_self_addr,
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Recr(_) =>
            let rec_wrapper = projection_addr(all_members, block_addr, pos);
            let rec_ci = load(get_ci(rec_wrapper));
            let is_match = match rec_ci {
              KConstantInfo.Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) =>
                let parent = rec_to_parent_addr(ty, np, nmot, nmin, ni);
                let parent_ci = load(get_ci(parent));
                let pnp = match parent_ci {
                  KConstantInfo.Induct(_, _, p, _, _, _, _, _) => p,
                  _ => 0,
                };
                let addr_m = address_eq(parent, target_ind_addr);
                match addr_m {
                  1 =>
                    match target_is_aux {
                      0 => 1,
                      _ =>
                        let rec_sp = extract_aux_spec_params(ty, np,
                          nmot, nmin, ni, pnp);
                        spec_params_ptr_eq(rec_sp, target_sp),
                    },
                  _ => 0,
                },
              _ => 0,
            };
            match is_match {
              1 => rec_wrapper,
              _ =>
                find_peer_rec_spec_walk(all_members, rest, block_addr,
                  target_ind_addr, target_sp, target_is_aux,
                  rec_self_addr, pos + 1),
            },
          _ =>
            find_peer_rec_spec_walk(all_members, rest, block_addr,
              target_ind_addr, target_sp, target_is_aux, rec_self_addr,
              pos + 1),
        },
    }
  }

  -- Build list of flat member own_params (num_params from each member's
  -- KCI). Used by build_ih_doms for target_n_params lookup.
  fn build_flat_own_params(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›)
                                  -> List‹G› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (member_addr, _is_aux, _sp, _ou) =>
            let ci = load(get_ci(member_addr));
            let np = match ci {
              KConstantInfo.Induct(_, _, n, _, _, _, _, _) => n,
              _ => 0,
            };
            store(ListNode.Cons(np,
              build_flat_own_params(rest))),
        },
    }
  }

  -- Synthesize a Ctor's CPrj wrapper addr.
  -- Bytes = put_constant(Constant{info: CPrj{idx, cidx, block_addr}, ...}).
  fn projection_addr_ctor(ind_idx: G, cidx: G,
                                block_addr: Addr) -> Addr {
    let idx_u64 = idx_to_u64(ind_idx);
    let cidx_u64 = idx_to_u64(cidx);
    let info = ConstantInfo.CPrj(ConstructorProj.Mk(idx_u64, cidx_u64,
      block_addr));
    let proj_c = Constant.Mk(info,
      store(ListNode.Nil), store(ListNode.Nil), store(ListNode.Nil));
    let bytes = put_constant(proj_c, store(ListNode.Nil));
    bytes_to_addr(bytes)
  }

  -- Iterate ctors 0..num_ctors-1, build minor for each via
  -- build_minor_at_depth. Return list of minor doms.
  fn build_minor_doms(member_addr: Addr, is_aux: G,
                            spec_params: List‹KExpr›,
                            occurrence_us: List‹KLevel›,
                            flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                            flat_own_params: List‹G›,
                            n_rec_params: G, n_motives: G,
                            motive_base: G, self_mem_idx: G,
                            block_addr: Addr, ind_idx: G,
                            num_ctors: G, prev_minors: G,
                            cidx: G) -> List‹KExpr› {
    match num_ctors - cidx {
      0 => store(ListNode.Nil),
      _ =>
        let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, cidx));
        match ctor_ci {
          KConstantInfo.Ctor(_, ctor_ty, _, _, _, np, _nf, _) =>
            let ctor_addr = projection_addr_ctor(ind_idx, cidx, block_addr);
            let minor = build_minor_at_depth(ctor_addr, ctor_ty, np,
              is_aux, spec_params, occurrence_us, flat, flat_own_params,
              n_rec_params, n_motives, prev_minors, motive_base,
              self_mem_idx);
            store(ListNode.Cons(minor,
              build_minor_doms(member_addr, is_aux, spec_params,
                occurrence_us, flat, flat_own_params, n_rec_params,
                n_motives, motive_base, self_mem_idx, block_addr, ind_idx,
                num_ctors, prev_minors + 1, cidx + 1))),
          -- No tolerant arm on purpose. Returning Nil for a non-Ctor would
          -- yield a canonical type with FEWER minor premises than the
          -- inductive has constructors, and the declared type is
          -- adversary-supplied, so it could be built to match the truncated
          -- reconstruction. Falling off the match rejects instead.
        },
    }
  }

  -- Iterate flat, per member call build_minor_doms with appropriate
  -- block_addr/ind_idx (from member_addr's KCI).
  fn build_all_minors(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                            flat_own_params: List‹G›,
                            n_rec_params: G, n_motives: G,
                            motive_base: G) -> List‹KExpr› {
    build_all_minors_walk(flat, flat, flat_own_params, n_rec_params,
      n_motives, motive_base, 0, 0)
  }

  -- Two flat lists on purpose. `flat` shrinks as the walk consumes members;
  -- `full_flat` stays pinned to the caller's original list and is what
  -- reaches `build_minor_doms`, so `is_rec_field` sees EVERY block member
  -- when matching spec_params. Passing the shrinking list down instead
  -- would make a later member's ctor-field classification blind to the
  -- members already consumed, silently dropping their induction hypotheses.
  fn build_all_minors_walk(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                                 full_flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                                 flat_own_params: List‹G›,
                                 n_rec_params: G, n_motives: G,
                                 motive_base: G, prev_minors: G,
                                 mem_pos: G) -> List‹KExpr› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (member_addr, is_aux, spec_params, occ_us) =>
            let ci = load(get_ci(member_addr));
            match ci {
              KConstantInfo.Induct(_, _, _, _, num_ctors, _,
                                     mem_block_addr, mem_ind_idx) =>
                let m_minors = build_minor_doms(member_addr, is_aux,
                  spec_params, occ_us, full_flat, flat_own_params,
                  n_rec_params, n_motives, motive_base, mem_pos,
                  mem_block_addr, mem_ind_idx, num_ctors, prev_minors, 0);
                let added = list_length(m_minors);
                let rest_minors = build_all_minors_walk(rest, full_flat,
                  flat_own_params, n_rec_params, n_motives, motive_base,
                  prev_minors + added, mem_pos + 1);
                list_concat(m_minors, rest_minors),
              _ =>
                build_all_minors_walk(rest, full_flat, flat_own_params,
                  n_rec_params, n_motives, motive_base, prev_minors,
                  mem_pos + 1),
            },
        },
    }
  }

  -- Peel n Foralls; per-index substitution.
  --   non-aux: BVar(depth - 1 - j).
  --   aux: spec_params[j] lifted by spec_lift when j < |spec|, else
  --        BVar(depth - 1 - j).
  fn ctor_subst_param_for(j: G, depth: G, spec_lift: G, is_aux: G,
                                spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => store(KExprNode.BVar((depth - 1) - j)),
      _ =>
        let len = list_length(spec_params);
        match u32_less_than(j, len) {
          1 => expr_lift(list_lookup(spec_params, j), spec_lift, 0),
          _ => store(KExprNode.BVar((depth - 1) - j)),
        },
    }
  }

  -- Count remaining leading Foralls in a type (until non-Forall).
  fn count_foralls_body(ty: KExpr, acc: G) -> G {
    match load(ty) {
      KExprNode.Forall(_, body) => count_foralls_body(body, acc + 1),
      _ => acc,
    }
  }

  -- Peel ctor's own_params with depth-aware substitution. For non-aux:
  -- BVar(depth-1-j). For aux: spec_params[j] lifted by `spec_lift`
  -- (binders between the recursor-param frame and the peel point — NOT
  -- `depth`, which counts the params themselves too) when j < |spec|;
  -- BVar(depth-1-j) otherwise.
  fn peel_ctor_params_subst(ty: KExpr, n: G, depth: G, spec_lift: G,
                                  is_aux: G, spec_params: List‹KExpr›,
                                  j: G) -> KExpr {
    match n {
      0 => ty,
      _ =>
        -- Structural first, reduce only as a fallback: a constructor's
        -- parameter binder can hide behind a definitional wrapper, and
        -- stopping short there builds a minor premise with fewer binders
        -- than the constructor actually has.
        match load(ty) {
          KExprNode.Forall(_, body) =>
            let p = ctor_subst_param_for(j, depth, spec_lift, is_aux,
              spec_params);
            let body_substed = expr_inst1(body, p, 0);
            peel_ctor_params_subst(body_substed, n - 1, depth,
              spec_lift, is_aux, spec_params, j + 1),
          _ =>
            match load(whnf(ty, store(ListNode.Nil))) {
              KExprNode.Forall(_, body) =>
                let p = ctor_subst_param_for(j, depth, spec_lift, is_aux,
                  spec_params);
                let body_substed = expr_inst1(body, p, 0);
                peel_ctor_params_subst(body_substed, n - 1, depth,
                  spec_lift, is_aux, spec_params, j + 1),
            },
        },
    }
  }

  -- Build minor binder type for one ctor. Mirror build_minor_at_depth
  -- (Inductive.lean:928-986).
  fn build_minor_at_depth(ctor_addr: Addr, ctor_ty: KExpr,
                                n_own_params: G,
                                is_aux: G, spec_params: List‹KExpr›,
                                occurrence_us: List‹KLevel›,
                                flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                                flat_own_params: List‹G›,
                                n_rec_params: G, n_motives: G,
                                prev_minors: G, motive_base: G,
                                self_mem_idx: G) -> KExpr {
    let ctor_ty_inst = expr_inst_levels(ctor_ty, occurrence_us);
    let minor_saved = n_rec_params + n_motives + prev_minors;
    let below_params = n_motives + prev_minors;
    let after_params = peel_ctor_params_subst(ctor_ty_inst, n_own_params,
      minor_saved, below_params, is_aux, spec_params, 0);
    match walk_fields_classify(after_params, flat, store(ListNode.Nil),
            store(ListNode.Nil), store(ListNode.Nil), 0, below_params) {
      (field_doms, rec_indices, rec_member_idxs, ret_ty) =>
        let n_fields = list_length(field_doms);
        let n_ihs = list_length(rec_indices);
        let n_binders = n_fields + n_ihs;
        let depth_now = minor_saved + n_binders;
        match collect_spine(ret_ty) {
          (_ret_head, ret_args) =>
            let ret_indices = list_drop(ret_args, n_own_params);
            let ret_indices_lifted = list_lift_each(ret_indices, n_ihs, 0);
            let motive_var = (depth_now - 1) - (motive_base + self_mem_idx);
            let motive_ref = store(KExprNode.BVar(motive_var));
            let with_indices = apply_spine_expr(motive_ref,
              ret_indices_lifted);
            let ctor_head = store(KExprNode.Const(ctor_addr, occurrence_us));
            let with_params = build_ctor_app_params(ctor_head,
              n_own_params, n_rec_params, depth_now, is_aux, spec_params);
            let ctor_app = build_apply_field_bvars(with_params,
              n_fields, n_binders, 0);
            let conclusion = store(KExprNode.App(with_indices, ctor_app));
            let ih_doms = build_ih_doms(rec_indices, rec_member_idxs,
              field_doms, flat_own_params, motive_base, n_fields,
              minor_saved, 0);
            let with_ihs = wrap_foralls(conclusion, ih_doms);
            wrap_foralls(with_ihs, field_doms),
        },
    }
  }

  -- Peel leading Foralls off `ty`, return (forall_doms, body).
  fn peel_leading_foralls(ty: KExpr) -> (List‹KExpr›, KExpr) {
    let pair = peel_leading_foralls_acc(ty, store(ListNode.Nil));
    match pair {
      (rev_acc, body) => (list_reverse(rev_acc), body),
    }
  }

  fn peel_leading_foralls_acc(ty: KExpr, acc: List‹KExpr›)
                                    -> (List‹KExpr›, KExpr) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        peel_leading_foralls_acc(body, store(ListNode.Cons(dom, acc))),
      _ => (acc, ty),
    }
  }

  fn build_apply_xs(head: KExpr, n_xs: G, i: G) -> KExpr {
    match n_xs - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar((n_xs - 1) - i));
        build_apply_xs(store(KExprNode.App(head, v)), n_xs, i + 1),
    }
  }

  -- Build IH dom per rec field. IH shape:
  --   ∀ (xs from Forall-in-dom peel), motive_ref (lifted_idx_args) (field_ref applied to xs)
  -- Mirror build_ih_doms (Inductive.lean:3286+).
  fn build_ih_doms(rec_indices: List‹G›, rec_member_idxs: List‹G›,
                        field_doms: List‹KExpr›,
                        flat_own_params: List‹G›,
                        motive_base: G, n_fields: G, minor_saved: G,
                        k: G) -> List‹KExpr› {
    match load(rec_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(field_idx, rest) =>
        let mem_idx = list_lookup_or_default(rec_member_idxs, k, 0);
        let target_n_params = list_lookup_or_default(flat_own_params,
          mem_idx, 0);
        let depth = minor_saved + n_fields + k;
        let dom = list_lookup(field_doms, field_idx);
        let dom_lifted = expr_lift(dom, (n_fields - field_idx) + k, 0);
        match peel_leading_foralls(dom_lifted) {
          (forall_doms, inner_body) =>
            let n_xs = list_length(forall_doms);
            let inner_depth = depth + n_xs;
            let motive_bvar = (inner_depth - 1) - (motive_base + mem_idx);
            let field_bvar = (inner_depth - 1) - (minor_saved + field_idx);
            -- Reduce before reading the spine: a recursive field written
            -- through a reducible wrapper (`Box M`) has that wrapper as its
            -- head, so its argument would be taken for an index and the
            -- induction hypothesis would apply the motive to one argument
            -- too many.
            match collect_spine(whnf(inner_body, store(ListNode.Nil))) {
              (_h, dom_args) =>
                let idx_args = list_drop(dom_args, target_n_params);
                let motive_ref = store(KExprNode.BVar(motive_bvar));
                let with_indices = apply_spine_expr(motive_ref, idx_args);
                let field_ref = store(KExprNode.BVar(field_bvar));
                let field_app = build_apply_xs(field_ref, n_xs, 0);
                let ih_body = store(KExprNode.App(with_indices, field_app));
                let ih_dom = wrap_foralls(ih_body, forall_doms);
                store(ListNode.Cons(ih_dom,
                  build_ih_doms(rest, rec_member_idxs, field_doms,
                    flat_own_params, motive_base, n_fields, minor_saved,
                    k + 1))),
            },
        },
    }
  }

  -- Lift each expr in a list by (shift, cutoff).
  fn list_lift_each(es: List‹KExpr›, shift: G, cutoff: G)
                          -> List‹KExpr› {
    match load(es) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(e, rest) =>
        store(ListNode.Cons(expr_lift(e, shift, cutoff),
          list_lift_each(rest, shift, cutoff))),
    }
  }

  -- Apply head to BVars at descending positions: BVar(start), BVar(start-1),
  -- ..., BVar(start - n + 1).
  fn build_apply_bvars_decreasing(head: KExpr, n: G, start: G,
                                        j: G) -> KExpr {
    match n - j {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - j));
        build_apply_bvars_decreasing(store(KExprNode.App(head, v)),
          n, start, j + 1),
    }
  }

  -- Apply head to ctor fields at BVar(n_binders-1)..BVar(n_binders-nf).
  fn build_apply_field_bvars(head: KExpr, n_fields: G, n_binders: G,
                                   i: G) -> KExpr {
    match n_fields - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar((n_binders - 1) - i));
        build_apply_field_bvars(store(KExprNode.App(head, v)),
          n_fields, n_binders, i + 1),
    }
  }

  -- Build ctor app with own_params: non-aux uses recursor param BVars,
  -- aux uses spec_params lifted.
  fn build_ctor_app_params(head: KExpr, n_own_params: G, n_rec_params: G,
                                 depth_now: G, is_aux: G,
                                 spec_params: List‹KExpr›) -> KExpr {
    match is_aux {
      0 => build_apply_bvars_decreasing(head, n_rec_params,
             depth_now - 1, 0),
      _ => apply_spec_params_lifted(head, spec_params,
             depth_now - n_rec_params),
    }
  }

  -- Given a field dom, check if it targets a flat member. Returns
  -- (found=0/1, mem_pos). For non-aux member: dom's head Const addr
  -- equals member's addr. For aux member: additionally dom's spine
  -- args[0..|spec_params|) match spec_params (each lifted by
  -- spec_lift_by binders). Nested-forall dom (Acc.intro's h :
  -- ∀ y, r y x → Acc r y) — peel leading Foralls until ret type
  -- and check its head.
  fn is_rec_field(dom: KExpr,
                       flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                       spec_lift_by: G) -> (G, G) {
    is_rec_field_peel(dom, flat, spec_lift_by)
  }

  -- WHNF, peel ONE Forall, repeat. Reducing at every peel is what
  -- exposes an inductive head written behind a reducible definition
  -- (`abbrev Box a := a` used as a ctor field `Box T`) and index binders
  -- hidden under definitional wrappers. Without it such a field is
  -- classified NOT recursive, the reconstructed rule omits its induction
  -- hypothesis, and `compare_rules` then disagrees with the real
  -- recursor.
  --
  -- WHNF runs in the EMPTY context on purpose: the peeled binder domains
  -- are deliberately not pushed. The body's loose BVars (field locals and
  -- the caller frame's param refs) are stuck under whnf either way, and a
  -- context built from local doms violates ctx-trim's frame
  -- well-formedness — a param-referencing dom's lbr exceeds the depth
  -- below it, running the context cut off the end of the list.
  fn is_rec_field_peel(ty: KExpr, flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                            spec_lift_by: G) -> (G, G) {
    let w = whnf(ty, store(ListNode.Nil));
    match load(w) {
      KExprNode.Forall(_, body) =>
        is_rec_field_peel(body, flat, spec_lift_by),
      _ =>
        match collect_spine(w) {
          (head, args) =>
            match load(head) {
              KExprNode.Const(caddr, _) =>
                flat_find_matching(flat, caddr, args, spec_lift_by, 0),
              _ => (0, 0),
            },
        },
    }
  }

  fn peel_leading_foralls_body(e: KExpr) -> KExpr {
    match load(e) {
      KExprNode.Forall(_, body) => peel_leading_foralls_body(body),
      _ => e,
    }
  }

  -- Walk flat, find entry whose addr matches AND (for aux) whose
  -- spec_params match dom_args' prefix (lifted).
  fn flat_find_matching(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                              caddr: Addr, dom_args: List‹KExpr›,
                              spec_lift_by: G, pos: G) -> (G, G) {
    match load(flat) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(m, rest) =>
        match m {
          (member_addr, is_aux, sp, _) =>
            let addr_match = address_eq(member_addr, caddr);
            let spec_match = match is_aux {
              0 => 1,
              _ => spec_params_dom_prefix_match(sp, dom_args,
                     spec_lift_by),
            };
            match addr_match * spec_match {
              1 => (1, pos),
              _ => flat_find_matching(rest, caddr, dom_args,
                     spec_lift_by, pos + 1),
            },
        },
    }
  }

  -- Compare spec_params (lifted) against the dom_args prefix. FAIL-OPEN:
  -- a wrong "no match" makes `is_rec_field` answer "not recursive",
  -- omitting an induction hypothesis from the reconstructed rule. The
  -- lifted spec param need not be pointer-identical to the argument even
  -- when structurally equal, so compare structurally.
  fn spec_params_dom_prefix_match(sp: List‹KExpr›,
                                        args: List‹KExpr›,
                                        lift_by: G) -> G {
    match load(sp) {
      ListNode.Nil => 1,
      ListNode.Cons(s, sr) =>
        match load(args) {
          ListNode.Nil => 0,
          ListNode.Cons(a, ar) =>
            let s_lifted = expr_lift(s, lift_by, 0);
            match kexpr_struct_eq(s_lifted, a) {
              1 => spec_params_dom_prefix_match(sr, ar, lift_by),
              _ => 0,
            },
        },
    }
  }

  -- Walk ctor body's field Foralls, collect (field_doms, rec_indices,
  -- rec_member_idxs, ret_ty). Field is recursive iff dom targets a
  -- flat member.
  fn walk_fields_classify(ty: KExpr,
                                flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                                doms_acc: List‹KExpr›, rec_acc: List‹G›,
                                rec_mem_acc: List‹G›,
                                fidx: G, spec_lift_by: G)
                                -> (List‹KExpr›, List‹G›, List‹G›, KExpr) {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        -- The lift grows with the field walk. `spec_params` live in the
        -- recursor-param frame; each field descended past adds one binder
        -- between that frame and this domain, so they must be lifted by
        -- `spec_lift_by + fidx` to compare against the domain's argument
        -- prefix. The `+ fidx` is load-bearing: without it every recursive
        -- field after the first fails to match its aux flat member and
        -- silently loses its induction hypothesis.
        let r = is_rec_field(dom, flat, spec_lift_by + fidx);
        let new_doms = store(ListNode.Cons(dom, doms_acc));
        match r {
          (1, mem_idx) =>
            let new_rec = store(ListNode.Cons(fidx, rec_acc));
            let new_mem = store(ListNode.Cons(mem_idx, rec_mem_acc));
            walk_fields_classify(body, flat, new_doms, new_rec,
              new_mem, fidx + 1, spec_lift_by),
          _ =>
            walk_fields_classify(body, flat, new_doms, rec_acc,
              rec_mem_acc, fidx + 1, spec_lift_by),
        },
      _ => (list_reverse(doms_acc), list_reverse(rec_acc),
              list_reverse(rec_mem_acc), ty),
    }
  }

  fn build_all_motives_walk(flat: List‹(Addr, G, List‹KExpr›, List‹KLevel›)›,
                                  elim_level: KLevel, n_rec_params: G,
                                  j: G) -> List‹KExpr› {
    match load(flat) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          (member_addr, is_aux, spec_params, occ_us) =>
            let ci = load(get_ci(member_addr));
            match ci {
              KConstantInfo.Induct(_, m_ind_ty, m_own_params, m_n_indices,
                                     _, _, _, _) =>
                let mt = build_motive_type_flat(member_addr, m_ind_ty,
                  m_own_params, m_n_indices, occ_us, elim_level,
                  n_rec_params, is_aux, spec_params);
                let mt_lifted = expr_lift(mt, j, 0);
                store(ListNode.Cons(mt_lifted,
                  build_all_motives_walk(rest, elim_level, n_rec_params,
                    j + 1))),
              _ =>
                build_all_motives_walk(rest, elim_level, n_rec_params, j),
            },
        },
    }
  }

  -- Synthesize aux ctor's body-typed form: peel n_own_params Foralls,
  -- substitute the peeled BVars with spec_params (each spec_param lives
  -- in recursor's outer scope — no lift needed when substituted at
  -- depth 0 within the peeled body).
  fn synth_aux_ctor_ty(ctor_ty: KExpr, n_own_params: G,
                             spec_params: List‹KExpr›) -> KExpr {
    let after_params = peel_n_foralls_tolerant(ctor_ty, n_own_params);
    -- BVars 0..n_own_params-1 in `after_params` refer to peeled param
    -- Foralls (innermost = last-peeled). expr_inst_many substitutes
    -- BVar(depth), BVar(depth+1), ..., BVar(depth+n-1) with substs[0],
    -- ..., substs[n-1]. Order matters: peel outermost first, so
    -- outermost peel-target = BVar(n_own_params-1). Reverse spec_params
    -- so substs[0] matches BVar(0) = innermost peel-target.
    expr_inst_many(after_params, list_reverse(spec_params), 0)
  }

  -- Aux canonical rhs: input ctor_body = synth_aux_ctor_ty's result
  -- (params substituted, ready to walk fields). Uses rec's own n_p
  -- (not ext's) for body_depth. Detection block_addrs includes BOTH
  -- rec_block_addr (for own-block direct-rec fields via peer recursor)
  -- AND parent_block_addr (for aux-self-recursion via ext parent).
  fn canonical_aux_body(cidx: G, num_ctors: G, rec_np: G, rec_ni: G,
                              nf: G, ctor_body: KExpr,
                              rec_block_addr: Addr,
                              parent_block_addr: Addr,
                              rec_self_addr: Addr, rec_nlvls: G) -> KExpr {
    let base = canonical_norec_body(cidx, num_ctors, rec_np, nf);
    let body_depth = (rec_np + 1 + num_ctors) + nf;
    let block_addrs = store(ListNode.Cons(rec_block_addr,
      store(ListNode.Cons(parent_block_addr, store(ListNode.Nil)))));
    let rec_infos = walk_fields_multi(ctor_body, block_addrs, 0);
    apply_ihs(base, rec_infos, rec_np, rec_ni, nf, body_depth,
      num_ctors, rec_block_addr, rec_self_addr, rec_nlvls)
  }

  fn walk_fields_multi(ty: KExpr, block_addrs: List‹Addr›,
                            field_pos: G) -> List‹(G, KExpr)› {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let mentions = expr_mentions_block(dom, block_addrs);
        let is_direct_rec = match mentions {
          0 => 0,
          _ => is_direct_rec_dom(dom),
        };
        let rest = walk_fields_multi(body, block_addrs, field_pos + 1);
        match is_direct_rec {
          1 => store(ListNode.Cons((field_pos, dom), rest)),
          _ => rest,
        },
      _ => store(ListNode.Nil),
    }
  }


  fn check_recursor_member(rec_ci: KConstantInfo, addr: Addr) {
    match rec_ci {
      KConstantInfo.Rec(nlvls, ty, n_p, n_i, n_mot, n_min, rules, k_flag,
                          _uns, rec_block_addr, _rec_idx) =>
        let parent_addr = rec_to_parent_addr(ty, n_p, n_mot, n_min, n_i);
        let parent_ci = load(get_ci(parent_addr));
        match parent_ci {
          KConstantInfo.Induct(_parent_nlvls, _, parent_np, parent_ni,
                                 num_ctors, _,
                                 parent_block_addr, parent_ind_idx) =>
            -- Aux iff rec's block_addr != parent's block_addr (parent
            -- is external — an aux member of rec's block for nested-ext
            -- traversal). Aux recursors have different arities than the
            -- ext parent (spec_params absorbed); shape checks against
            -- parent's arity don't apply. Keep only well-scoped +
            -- rule-count sanity.
            -- Aux only when BOTH rec's and parent's blocks are Muts,
            -- and they differ. Anon representations may wrap a single
            -- Recr in a singleton Muts with parent stored standalone
            -- — that's not "aux", just anonymization.
            let is_aux = is_muts_block(rec_block_addr) *
              is_muts_block(parent_block_addr) *
              (1 - address_eq(rec_block_addr, parent_block_addr));
            assert_eq!(list_length(rules), num_ctors,
              "recursor rule count differs from the inductive's ctor count");
            peel_n_foralls(ty,
              ((n_p + n_mot) + n_min + n_i) + 1);
            check_rec_rules_wellscoped(rules,
              n_p + n_mot + n_min, nlvls);
            -- Arity checks compare against the PARENT's counts, which only
            -- coincide with the recursor's when it eliminates that parent
            -- directly. An aux recursor absorbs the nesting's spec params,
            -- so its arities legitimately differ and these do not apply to
            -- it. Motive and minor premises, index binders, the major spine
            -- and the conclusion are covered for BOTH cases by the declared
            -- type's def-eq against the canonical reconstruction below, so
            -- skipping these for aux loses nothing.
            match is_aux {
              1 => (),
              _ =>
                assert_eq!(n_p, parent_np,
                  "recursor parameter count differs from its inductive's");
                assert_eq!(n_i, parent_ni,
                  "recursor index count differs from its inductive's");
                check_rec_major_spine(ty, n_p, n_mot, n_min, n_i,
                                           parent_np + parent_ni),
            };
            -- Unconditional: neither depends on the recursor eliminating its
            -- parent directly, and `is_aux` is a function of WHERE the Recr
            -- was placed, so gating on it let a recursor declared outside its
            -- parent's block skip both.
            --
            -- `k_flag` is not part of the recursor's type, so the def-eq
            -- check cannot catch a forged one — and a wrong k_flag enables
            -- K-style reduction that the inductive does not license.
            let computed_k = compute_k_target(parent_ci, parent_addr);
            assert_eq!(k_flag, computed_k,
              "recursor k_flag disagrees with its inductive's K eligibility");
            -- A recursor's meaning is only well-defined over a well-formed
            -- inductive: the elimination rules it encodes are derived from
            -- the ctor telescopes. Under subject-only checking, `<ind>.rec`
            -- is reachable without ever checking `<ind>` itself (memoized
            -- per block — the inductive's own check_const hits the same rows).
            check_parent_inductive_shape(parent_ci);
            -- Full canonical rules identity check via reference-parallel pipeline.
            check_recursor_canonical_full(rec_ci, addr, parent_ci, parent_addr),
        },
    }
  }

  fn check_rec_major_spine(ty: KExpr, n_p: G, n_mot: G, n_min: G,
                                n_i: G, expected_args: G) {
    let skip = n_p + n_mot + n_min + n_i;
    let after_skip = peel_n_foralls(ty, skip);
    match load(after_skip) {
      KExprNode.Forall(major_ty, _) =>
        match collect_spine(major_ty) {
          (_head, args) =>
            assert_eq!(list_length(args), expected_args,
              "recursor major premise has the wrong number of spine args");
            (),
        },
    }
  }

  -- Phase 2b (partial): rule shape sanity.
  -- Per stored rule:
  --   * cidx sequences from 0 to num_ctors-1 in order.
  --   * cidx < num_ctors.
  --   * num_args == parent ctor's (num_params + num_fields).
  -- Skips canonical rhs identity (phase 2b-full) — construction requires
  -- build_rec_type + populate_rules + full aux/nested machinery
  -- (~2000 LOC positional→addr-first port).
  -- Solo detection: block_addr == parent addr OR Muts w/ 1 Indc member.
  fn ctor_has_rec_fields_solo(ctor_ty: KExpr, n_params: G,
                                    parent_addr: Addr) -> G {
    let after_params = peel_n_foralls_tolerant(ctor_ty, n_params);
    let block_addrs = store(ListNode.Cons(parent_addr, store(ListNode.Nil)));
    scan_fields_for_block_ref(after_params, block_addrs)
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

  fn scan_fields_for_block_ref(ty: KExpr, block_addrs: List‹Addr›) -> G {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match expr_mentions_block(dom, block_addrs) {
          1 => 1,
          _ => scan_fields_for_block_ref(body, block_addrs),
        },
      _ => 0,
    }
  }

  -- Build App(head, BVar(nf-1)) App(_, BVar(nf-2)) ... App(_, BVar(0))
  fn apply_field_bvars(head: KExpr, nf: G, i: G) -> KExpr {
    match nf - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar((nf - 1) - i));
        apply_field_bvars(store(KExprNode.App(head, v)), nf, i + 1),
    }
  }

  -- Canonical rhs BODY (Lams peeled) for a solo ctor rule (any ctor).
  -- body_depth = n_p + n_mot(=1) + n_min(=num_ctors) + nf.
  -- Body: minor applied to fields, then IHs (one per rec field).
  fn canonical_norec_body(cidx: G, num_ctors: G, n_p: G,
                                nf: G) -> KExpr {
    let body_depth = (n_p + 1 + num_ctors) + nf;
    let minor_var = (body_depth - 1) - ((n_p + 1) + cidx);
    let minor = store(KExprNode.BVar(minor_var));
    apply_field_bvars(minor, nf, 0)
  }

  -- Extended canonical body: adds IHs for rec fields. Handles solo and
  -- mutual blocks; peer recursor addr resolved per-field via
  -- find_peer_recursor.
  fn canonical_body(cidx: G, num_ctors: G, n_p: G, n_i: G,
                         nf: G, ctor_ty: KExpr, block_addr: Addr,
                         rec_self_addr: Addr, rec_nlvls: G,
                         rec_block_addr: Addr) -> KExpr {
    let base = canonical_norec_body(cidx, num_ctors, n_p, nf);
    let body_depth = (n_p + 1 + num_ctors) + nf;
    let rec_infos = collect_rec_field_infos(ctor_ty, n_p, block_addr);
    apply_ihs(base, rec_infos, n_p, n_i, nf, body_depth,
      num_ctors, rec_block_addr, rec_self_addr, rec_nlvls)
  }

  -- Rec field info: (position, dom). Both used by IH construction:
  -- position for field BVar index, dom for extracting index args.
  fn collect_rec_field_infos(ty: KExpr, np: G,
                                   block_addr: Addr) -> List‹(G, KExpr)› {
    let after_params = peel_n_foralls_tolerant(ty, np);
    walk_fields_collect_rec_infos(after_params, block_addr, 0)
  }

  fn walk_fields_collect_rec_infos(ty: KExpr, block_addr: Addr,
                                        field_pos: G) -> List‹(G, KExpr)› {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let block_addrs = store(ListNode.Cons(block_addr,
          store(ListNode.Nil)));
        let mentions = expr_mentions_block(dom, block_addrs);
        let is_direct_rec = match mentions {
          0 => 0,
          _ => is_direct_rec_dom(dom),
        };
        let rest_infos = walk_fields_collect_rec_infos(body, block_addr,
          field_pos + 1);
        match is_direct_rec {
          1 => store(ListNode.Cons((field_pos, dom), rest_infos)),
          _ => rest_infos,
        },
      _ => store(ListNode.Nil),
    }
  }

  -- For each rec field j, append IH_j applied to `head`.
  -- IH_j = `Const(target_rec, rec_lvls) (params...) (motives...) (minors...) (idx_args) field_j`.
  -- target_rec = peer_recs[mem_idx] — the recursor for the field's own type.
  -- Mirror crates/kernel/src/inductive.rs fn build_rule_ih.
  -- Mirror crates/kernel/src/inductive.rs fn build_rule_ih: WHNF the
  -- field's lifted dom and the inner body so the head/args reflect the
  -- true inductive occurrence (after reducing wrappers like
  -- `constType (n α) (n α)` → `n α`).
  fn apply_ihs(body: KExpr, rec_infos: List‹(G, KExpr)›,
                    n_p: G, n_i: G, nf: G, body_depth: G,
                    num_ctors: G, block_addr: Addr,
                    rec_self_addr: Addr, rec_nlvls: G) -> KExpr {
    match load(rec_infos) {
      ListNode.Nil => body,
      ListNode.Cons(info, rest) =>
        match info {
          (pos, dom) =>
            let ih = build_ih(pos, dom, n_p, n_i, nf, body_depth,
              num_ctors, block_addr, rec_self_addr, rec_nlvls);
            apply_ihs(store(KExprNode.App(body, ih)), rest,
              n_p, n_i, nf, body_depth, num_ctors, block_addr,
              rec_self_addr, rec_nlvls),
        },
    }
  }

  -- Build IH with indices extracted from the (lifted) field dom's spine.
  -- For mutual blocks, dom's head may be a PEER inductive — resolve its
  -- recursor via find_peer_recursor. For solo, dom's head == parent
  -- inductive, target rec = self.
  fn build_ih(pos: G, dom: KExpr, n_p: G, n_i: G, nf: G,
                   body_depth: G, num_ctors: G, block_addr: Addr,
                   rec_self_addr: Addr, rec_nlvls: G) -> KExpr {
    let dom_s1 = expr_lift(dom, nf - pos, 0);
    let dom_lifted = expr_lift(dom_s1, 1 + num_ctors, nf);
    let (dom_head, dom_args) = collect_spine(dom_lifted);
    let target_ind_addr = match load(dom_head) {
      KExprNode.Const(caddr, _) => caddr,
      _ => rec_self_addr,
    };
    let target_rec_addr = find_peer_recursor(block_addr,
      target_ind_addr, rec_self_addr);
    let lvls = build_rec_lvls_list(rec_nlvls, 0);
    let const_head = store(KExprNode.Const(target_rec_addr, lvls));
    let with_params = apply_param_bvars(const_head, n_p, body_depth - 1, 0);
    let motive_bvar = (body_depth - 1) - n_p;
    let with_motive = store(KExprNode.App(with_params,
      store(KExprNode.BVar(motive_bvar))));
    let minor_start = (body_depth - 1) - (n_p + 1);
    let with_minors = apply_minor_bvars(with_motive, num_ctors,
      minor_start, 0);
    let idx_args = list_drop(dom_args, n_p);
    let with_indices = apply_spine_expr(with_minors, idx_args);
    let field_bvar = (nf - 1) - pos;
    store(KExprNode.App(with_indices, store(KExprNode.BVar(field_bvar))))
  }

  -- Given a target inductive addr and the CHECKING recursor's OWN
  -- block_addr (Muts wrapper), find the recursor in that block whose
  -- parsed parent addr matches target. For aux recursors, walking
  -- rec's own block (not parent's ext block) locates both the aux self
  -- (for ext-target IHs) and the block members' peer recursors (for
  -- own-block-target IHs).
  fn find_peer_recursor(block_addr: Addr, target_ind_addr: Addr,
                             rec_self_addr: Addr) -> Addr {
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            find_peer_rec_walk(members, members, block_addr,
              target_ind_addr, rec_self_addr, 0),
          _ => rec_self_addr,
        },
    }
  }

  fn find_peer_rec_walk(all_members: List‹MutConst›,
                             cur: List‹MutConst›, block_addr: Addr,
                             target_ind_addr: Addr, rec_self_addr: Addr,
                             pos: G) -> Addr {
    match load(cur) {
      ListNode.Nil => rec_self_addr,
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Recr(_) =>
            -- Get this recursor's wrapper addr + KCI, parse ty for
            -- its parent inductive addr.
            let rec_wrapper = projection_addr(all_members, block_addr, pos);
            let rec_ci = load(get_ci(rec_wrapper));
            let parent_addr = match rec_ci {
              KConstantInfo.Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) =>
                rec_to_parent_addr(ty, np, nmot, nmin, ni),
              _ => rec_self_addr,
            };
            match address_eq(parent_addr, target_ind_addr) {
              1 => rec_wrapper,
              _ =>
                find_peer_rec_walk(all_members, rest, block_addr,
                  target_ind_addr, rec_self_addr, pos + 1),
            },
          _ =>
            find_peer_rec_walk(all_members, rest, block_addr,
              target_ind_addr, rec_self_addr, pos + 1),
        },
    }
  }

  fn apply_spine_expr(head: KExpr, args: List‹KExpr›) -> KExpr {
    match load(args) {
      ListNode.Nil => head,
      ListNode.Cons(a, rest) =>
        apply_spine_expr(store(KExprNode.App(head, a)), rest),
    }
  }

  -- Walk ctor's fields after peeling np params. For each Forall(dom, ..),
  -- if dom mentions block AND dom is Const-headed spine (no Forall, no
  -- other), append field's position. Returns positions of DIRECT-REC
  -- fields; returns (0, empty) if any complex case detected (bail).
  fn collect_rec_field_positions(ty: KExpr, np: G, block_addr: Addr,
                                       field_pos: G) -> List‹G› {
    let after_params = peel_n_foralls_tolerant(ty, np);
    walk_fields_collect_rec(after_params, block_addr, 0)
  }

  fn walk_fields_collect_rec(ty: KExpr, block_addr: Addr,
                                  field_pos: G) -> List‹G› {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let block_addrs = store(ListNode.Cons(block_addr,
          store(ListNode.Nil)));
        let mentions = expr_mentions_block(dom, block_addrs);
        let is_direct_rec = match mentions {
          0 => 0,
          _ => is_direct_rec_dom(dom),
        };
        let rest_positions = walk_fields_collect_rec(body, block_addr,
          field_pos + 1);
        match is_direct_rec {
          1 => store(ListNode.Cons(field_pos, rest_positions)),
          _ => rest_positions,
        },
      _ => store(ListNode.Nil),
    }
  }

  -- Direct-rec: dom = Const-headed spine (no Forall, no other complications).
  fn is_direct_rec_dom(dom: KExpr) -> G {
    match load(dom) {
      KExprNode.Forall(_, _) => 0,
      _ =>
        match collect_spine(dom) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(_, _) => 1,
              _ => 0,
            },
        },
    }
  }

  -- Apply IH for each rec field position.
  fn apply_ihs_solo(body: KExpr, rec_positions: List‹G›,
                        n_p: G, n_i: G, nf: G, body_depth: G,
                        num_ctors: G, rec_self_addr: Addr,
                        rec_nlvls: G) -> KExpr {
    match load(rec_positions) {
      ListNode.Nil => body,
      ListNode.Cons(pos, rest) =>
        let ih = build_ih_solo(pos, n_p, n_i, nf, body_depth,
          num_ctors, rec_self_addr, rec_nlvls);
        apply_ihs_solo(store(KExprNode.App(body, ih)), rest,
          n_p, n_i, nf, body_depth, num_ctors, rec_self_addr,
          rec_nlvls),
    }
  }

  -- Build IH for solo direct-rec field at position `pos`:
  --   `Rec.self.{Param(0)..Param(nlvls-1)}
  --     param_0 ... param_{np-1}
  --     motive
  --     minor_0 ... minor_{nc-1}
  --     (indices — skipped for direct-rec, would need dom's spine)
  --     field_pos`
  -- Field at BVar(nf-1-pos). motive at BVar(body_depth - 1 - np).
  -- minor_i at BVar(body_depth - 1 - np - 1 - i). Param_i at
  -- BVar(body_depth - 1 - i).
  -- Note: for n_i > 0 direct-rec, would need to extract indices from
  -- dom's spine; skipping means IH may be wrong for indexed inductives.
  -- Bail for n_i > 0 by returning a placeholder (comparison fails —
  -- caller should have filtered).
  fn build_ih_solo(pos: G, n_p: G, n_i: G, nf: G, body_depth: G,
                        num_ctors: G, rec_self_addr: Addr,
                        rec_nlvls: G) -> KExpr {
    let lvls = build_rec_lvls_list(rec_nlvls, 0);
    let const_head = store(KExprNode.Const(rec_self_addr, lvls));
    let with_params = apply_param_bvars(const_head, n_p, body_depth - 1, 0);
    let motive_bvar = (body_depth - 1) - n_p;
    let with_motive = store(KExprNode.App(with_params,
      store(KExprNode.BVar(motive_bvar))));
    let minor_start = (body_depth - 1) - (n_p + 1);
    let with_minors = apply_minor_bvars(with_motive, num_ctors,
      minor_start, 0);
    -- Skip indices (would need dom-spine extraction; solo direct-rec
    -- with n_i=0 only for this slice).
    let field_bvar = (nf - 1) - pos;
    store(KExprNode.App(with_minors,
      store(KExprNode.BVar(field_bvar))))
  }

  fn build_rec_lvls_list(total: G, i: G) -> List‹KLevel› {
    match total - i {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons(
          store(KLevelNode.Param(i)),
          build_rec_lvls_list(total, i + 1))),
    }
  }

  fn apply_param_bvars(head: KExpr, n: G, start: G, i: G) -> KExpr {
    match n - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - i));
        apply_param_bvars(store(KExprNode.App(head, v)), n, start, i + 1),
    }
  }

  fn apply_minor_bvars(head: KExpr, n: G, start: G, i: G) -> KExpr {
    match n - i {
      0 => head,
      _ =>
        let v = store(KExprNode.BVar(start - i));
        apply_minor_bvars(store(KExprNode.App(head, v)), n, start, i + 1),
    }
  }

  -- Walk each rule; assert its rhs is well-scoped under depth =
  -- outer_depth + rule.num_args (nf) and universe-bound nlvls.
  fn check_rec_rules_wellscoped(rules: List‹KRecRule›,
                                     outer_depth: G, nlvls: G) {
    match load(rules) {
      ListNode.Nil => (),
      ListNode.Cons(r, rest) =>
        match r {
          KRecRule.Mk(_, nf, rhs) =>
            validate_expr_well_scoped(rhs, outer_depth + nf, nlvls);
            check_rec_rules_wellscoped(rest, outer_depth, nlvls),
        },
    }
  }

  -- Aux-flavored rule walk: per rule, synth aux ctor_ty (peel + subst
  -- with spec_params), compute canonical body using rec's own n_p +
  -- multi-block-addr detection, def_eq compare against stored rhs.
  fn check_aux_rules_walk(rules: List‹KRecRule›,
                                parent_block_addr: Addr,
                                parent_ind_idx: G, num_ctors: G,
                                expected_cidx: G, parent_np: G,
                                parent_ni: G, spec_params: List‹KExpr›,
                                rec_np: G, rec_self_addr: Addr,
                                rec_nlvls: G,
                                rec_block_addr: Addr) {
    match load(rules) {
      ListNode.Nil => (),
      ListNode.Cons(r, rest) =>
        match r {
          KRecRule.Mk(cidx, num_args, rhs) =>
            assert_eq!(cidx, expected_cidx,
              "aux recursor rule is out of ctor order");
            assert_eq!(u32_less_than(cidx, num_ctors), 1,
              "aux recursor rule names a ctor index out of range");
            let ctor_ci = load(get_ci_cprj(parent_block_addr,
              parent_ind_idx, cidx));
            match ctor_ci {
              KConstantInfo.Ctor(_, ctor_ty, _, _, _, _cnp, nf, _) =>
                assert_eq!(num_args, nf,
                  "aux recursor rule field count differs from the ctor's");
                let total_lams = ((rec_np + 1) + num_ctors) + nf;
                let rhs_body = peel_n_lams(rhs, total_lams);
                -- Synthesize aux ctor body (params substituted).
                let aux_ctor_body = synth_aux_ctor_ty(ctor_ty,
                  parent_np, spec_params);
                let canonical = canonical_aux_body(cidx, num_ctors,
                  rec_np, parent_ni, nf, aux_ctor_body, rec_block_addr,
                  parent_block_addr, rec_self_addr, rec_nlvls);
                let types = build_dummy_types(total_lams,
                  store(ListNode.Nil));
                assert_eq!(k_is_def_eq(rhs_body, canonical, types), 1,
                  "aux recursor rule rhs differs from canonical reconstruction");
                check_aux_rules_walk(rest, parent_block_addr,
                  parent_ind_idx, num_ctors, cidx + 1, parent_np,
                  parent_ni, spec_params, rec_np, rec_self_addr,
                  rec_nlvls, rec_block_addr),
            },
        },
    }
  }

  fn check_rec_rules_walk(rules: List‹KRecRule›,
                               block_addr: Addr, ind_idx: G,
                               num_ctors: G, expected_cidx: G,
                               ni: G, rec_self_addr: Addr,
                               rec_nlvls: G, is_aux: G,
                               rec_block_addr: Addr) {
    match load(rules) {
      ListNode.Nil => (),
      ListNode.Cons(r, rest) =>
        match r {
          KRecRule.Mk(cidx, num_args, rhs) =>
            assert_eq!(cidx, expected_cidx,
              "recursor rule is out of ctor order");
            assert_eq!(u32_less_than(cidx, num_ctors), 1,
              "recursor rule names a ctor index out of range");
            let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, cidx));
            match ctor_ci {
              KConstantInfo.Ctor(_, ctor_ty, _, _, _, np, nf, _) =>
                assert_eq!(num_args, nf,
                  "recursor rule field count differs from the ctor's");
                -- Peel ALL outer Lams: n_p (params) + n_mot=1 (motive)
                -- + num_ctors (minors) + nf (fields).
                let total_lams = ((np + 1) + num_ctors) + nf;
                let rhs_body = peel_n_lams(rhs, total_lams);
                maybe_canonical_norec_check(cidx, num_ctors, np, nf,
                                                  ctor_ty, rhs_body,
                                                  block_addr, ind_idx,
                                                  ni, rec_self_addr,
                                                  rec_nlvls, is_aux,
                                                  rec_block_addr);
                check_rec_rules_walk(rest, block_addr, ind_idx,
                                          num_ctors, cidx + 1, ni,
                                          rec_self_addr, rec_nlvls,
                                          is_aux, rec_block_addr),
            },
        },
    }
  }

  -- Solo + non-recursive check. Bails if either:
  --   * parent isn't solo (Muts block w/ >1 Indc);
  --   * ctor has recursive fields (would require IH construction).
  -- Otherwise builds canonical body and def_eq compares to stored.
  fn maybe_canonical_norec_check(cidx: G, num_ctors: G, np: G, nf: G,
                                       ctor_ty: KExpr, rhs_body: KExpr,
                                       block_addr: Addr, ind_idx: G,
                                       ni: G, rec_self_addr: Addr,
                                       rec_nlvls: G, is_aux: G,
                                       rec_block_addr: Addr) {
    -- Bail if aux (needs flat_block/spec_params), if any field is
    -- nested-ext (dom mentions block but head is not a block-member
    -- Ind), or Forall-in-dom.
    let has_complex = ctor_has_complex_rec_field(ctor_ty, np, block_addr);
    match has_complex {
      1 => (),
      _ =>
        let canonical = canonical_body(cidx, num_ctors, np, ni, nf,
          ctor_ty, block_addr, rec_self_addr, rec_nlvls, rec_block_addr);
        let types = build_ctor_rule_types(ctor_ty, np, nf,
          num_ctors, store(ListNode.Nil));
        assert_eq!(k_is_def_eq(rhs_body, canonical, types), 1,
          "non-recursive ctor rule rhs differs from canonical reconstruction");
        (),
    }
  }

  -- Returns 1 if any field is nested-ext or Forall-in-dom.
  fn ctor_has_complex_rec_field(ctor_ty: KExpr, np: G,
                                      block_addr: Addr) -> G {
    let after_params = peel_n_foralls_tolerant(ctor_ty, np);
    scan_fields_for_complex(after_params, block_addr)
  }

  fn scan_fields_for_complex(ty: KExpr, block_addr: Addr) -> G {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        let block_addrs = store(ListNode.Cons(block_addr,
          store(ListNode.Nil)));
        let mentions = expr_mentions_block(dom, block_addrs);
        let is_complex = match mentions {
          0 => 0,
          _ => 1 - dom_head_is_block_member(dom, block_addr),
        };
        match is_complex {
          1 => 1,
          _ => scan_fields_for_complex(body, block_addr),
        },
      _ => 0,
    }
  }

  -- Returns 1 iff dom's spine head is Const of an Ind whose KCI's
  -- block_addr matches ours (direct-rec on block member). 0 for Forall,
  -- non-Const head, or ext-nested Const heads.
  fn dom_head_is_block_member(dom: KExpr, block_addr: Addr) -> G {
    match load(dom) {
      KExprNode.Forall(_, _) => 0,
      _ =>
        match collect_spine(dom) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(caddr, _) =>
                let ci = load(get_ci(caddr));
                match ci {
                  KConstantInfo.Induct(_, _, _, _, _, _, ba, _) =>
                    address_eq(ba, block_addr),
                  _ => 0,
                },
              _ => 0,
            },
        },
    }
  }

  -- Parent-addr resolution parallels ctor gauntlet's helper.
  fn ctor_parent_addr(block_addr: Addr, ind_idx: G) -> Addr {
    -- If block_addr is a Muts wrapper, parent addr = projection_addr
    -- (IPrj wrapper for the ind at ind_idx). If standalone, parent addr
    -- = block_addr itself. Detect Muts by loading and matching.
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            projection_addr(members, block_addr, ind_idx),
          _ => block_addr,
        },
    }
  }

  -- Build a types context for def_eq of rhs_body under body scope:
  --   [field_nf-1_dom, ..., field_0_dom, minor_{nc-1}_dom, ...,
  --    minor_0_dom, motive_dom, param_{np-1}_dom, ..., param_0_dom]
  -- Innermost first (as k_is_def_eq expects). For minimal check we
  -- only need enough context that k_is_def_eq's BVar-lookup won't
  -- panic — dummies for shape. Since we're comparing structural BVars
  -- against BVars (no whnf via ctx needed), types can be all dummies
  -- (Srt 0) of proper length.
  fn build_ctor_rule_types(ctor_ty: KExpr, np: G, nf: G,
                                 num_ctors: G,
                                 acc: List‹KExpr›) -> List‹KExpr› {
    -- Length = np + 1 (motive) + num_ctors (minors) + nf (fields).
    let total = ((np + 1) + num_ctors) + nf;
    build_dummy_types(total, acc)
  }

  -- Peel up to `n` Lams, collecting each binder's DOMAIN as we descend.
  -- The returned list is innermost-first, i.e. exactly the `types` context
  -- the peeled body needs.
  --
  -- This replaces `build_dummy_types` at the rule comparison. The old
  -- kernel compared the FULL rhs terms in an empty context, where each
  -- Lam carries its own domain; peeling the binders off and then filling
  -- the context with `Sort 0` placeholders left every minor and field
  -- typed as `Prop`, so inference inside `k_is_def_eq` aborted with
  -- "application of a non-function type" the moment a rule body actually
  -- applied a minor to its fields. Only bare-`BVar` bodies survived.
  fn peel_n_lams_collect(e: KExpr, n: G, peeled: G, acc: List‹KExpr›)
                              -> (KExpr, G, List‹KExpr›) {
    match n {
      0 => (e, peeled, acc),
      _ =>
        match load(e) {
          KExprNode.Lam(dom, body) =>
            peel_n_lams_collect(body, n - 1, peeled + 1,
              store(ListNode.Cons(dom, acc))),
          _ => (e, peeled, acc),
        },
    }
  }

  -- DO NOT USE for a context that inference will consult. Every entry is
  -- `Sort 0`, so any binder looked up through it types as `Prop` and the
  -- first application of it aborts with "application of a non-function
  -- type". Use `peel_n_lams_collect` to recover the real domains from the
  -- term's own binders. Its two remaining callers are in the dead chain
  -- (`check_aux_rules_walk`, `maybe_canonical_norec_check`) and carry this
  -- defect latently — fix them if that code is ever revived.
  fn build_dummy_types(n: G, acc: List‹KExpr›) -> List‹KExpr› {
    match n {
      0 => acc,
      _ =>
        let dummy = store(KExprNode.Srt(store(KLevelNode.Zero)));
        build_dummy_types(n - 1, store(ListNode.Cons(dummy, acc))),
    }
  }

  -- check_const: dispatch per KConstantInfo variant.
  fn check_const(ci: KConstantInfo, addr: Addr) {
    let u = is_unsafe_ci(ci);
    match ci {
      KConstantInfo.Axiom(nlvls, ty, _) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        k_ensure_sort(ty, store(ListNode.Nil));
        assert_safety(u, ty),
      KConstantInfo.Defn(nlvls, ty, val, _, _) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        validate_expr_well_scoped(val, 0, nlvls);
        k_ensure_sort(ty, store(ListNode.Nil));
        assert_safety(u, ty);
        assert_safety(u, val);
        k_check(val, ty, store(ListNode.Nil)),
      KConstantInfo.Thm(nlvls, ty, val) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        validate_expr_well_scoped(val, 0, nlvls);
        let lvl = k_ensure_sort(ty, store(ListNode.Nil));
        assert_eq!(level_equal(lvl, store(KLevelNode.Zero)), 1,
          "theorem's type is not a Prop");
        assert_safety(u, ty);
        assert_safety(u, val);
        k_check(val, ty, store(ListNode.Nil)),
      KConstantInfo.Opaque(nlvls, ty, val, _) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        validate_expr_well_scoped(val, 0, nlvls);
        k_ensure_sort(ty, store(ListNode.Nil));
        assert_safety(u, ty);
        assert_safety(u, val);
        k_check(val, ty, store(ListNode.Nil)),
      KConstantInfo.Quot(nlvls, ty, kind) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        k_ensure_sort(ty, store(ListNode.Nil));
        assert_safety(u, ty);
        check_quot(addr, kind, nlvls, ty),
      KConstantInfo.Induct(nlvls, ty, n_params, n_indices, num_ctors,
                            ind_is_unsafe, ind_block, ind_idx) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        k_ensure_sort(ty, store(ListNode.Nil));
        assert_safety(u, ty);
        -- Canonical block member ordering (adversarial threat model:
        -- reordered/alpha-colliding Muts members must be rejected).
        -- Memoized per block addr — runs once even though every
        -- member check invokes it.
        check_canonical_block(ind_block);
        -- Self-contained shape validation: result sort + the full
        -- per-ctor gauntlet. Without it, subject-only checking accepts
        -- an inductive whose badness lives in a ctor const.
        check_inductive_shape(ty, n_params, n_indices, num_ctors,
                                   nlvls, ind_block, ind_idx,
                                   ind_is_unsafe);
        check_block_peer_param_agreement(ci, addr),
      KConstantInfo.Ctor(nlvls, ty, block_addr, ind_idx, _cidx,
                         num_params, num_fields, _) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        k_ensure_sort(ty, store(ListNode.Nil));
        assert_safety(u, ty);
        let ind_ci = load(@ctor_parent_ind_ci(block_addr, ind_idx));
        match ind_ci {
          KConstantInfo.Induct(ind_nlvls, ind_ty, ind_n_params,
                                ind_n_indices, _, ind_is_unsafe, _, _) =>
            assert_eq!(num_params, ind_n_params,
              "ctor parameter count differs from its inductive's");
            check_param_agreement(ind_ty, ty, ind_n_params);
            check_ctor_return_type(ty, num_params, ind_n_indices,
                                        num_fields, ind_nlvls, block_addr,
                                        ind_idx);
            let ind_level = get_result_sort_level(ind_ty,
              ind_n_params + ind_n_indices, store(ListNode.Nil));
            check_field_universes(ty, num_params, ind_level);
            -- Positivity skipped for unsafe inductives — see
            -- check_inductive_shape_ctors.
            match ind_is_unsafe {
              0 => check_positivity(ty, num_params, block_addr,
                                         store(ListNode.Nil)),
              _ => (),
            },
        },
      KConstantInfo.Rec(nlvls, ty, _, _, _, _, _, _, _, rec_block, _) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        k_ensure_sort(ty, store(ListNode.Nil));
        assert_safety(u, ty);
        check_canonical_block(rec_block);
        check_recursor_member(ci, addr),
    }
  }
⟧

end IxVM

end
