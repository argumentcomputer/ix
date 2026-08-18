module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Levels
public import Ix.IxVM.Kernel.Klimbs
public import Ix.IxVM.Kernel.NatPrim
public import Ix.IxVM.Kernel.Whnf
public import Ix.IxVM.Kernel.InferOnly
public import Ix.IxVM.Ingress

public section

namespace IxVM

/-! ## Def-Eq

`k_is_def_eq(a, b, types) → 1 iff a ≡ b`. Decided by a ladder of tiers,
cheapest first, because the expensive tiers are the ones that unfold
definitions and can blow up:

pointer equality → memo lookup on a context-trimmed, pointer-ordered key
→ app congruence on a shared Const head (no unfolding) → string-literal
expansion → no-delta whnf (`whnf_nd`) plus `quick_def_eq` → proof
irrelevance → unit-like types → structure eta → Nat offset comparison →
lazy delta, unfolding the higher-ranked side first → full structural
compare.

Tier order is load-bearing rather than a matter of taste; where a tier's
position matters for correctness and not just cost, the reason is
recorded at that tier.
-/

def defEq := ⟦
  -- Level list equality (semantic, uses level normalization).
  fn level_list_eq(a: List‹KLevel›, b: List‹KLevel›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(x, xs) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(y, ys) =>
            match level_equal(x, y) {
              0 => 0,
              _ => level_list_eq(xs, ys),
            },
        },
    }
  }

  -- Main entry: def-eq of two KExpr in a shared types context.
  -- Context-trimmed memo key (mirror k_is_def_eq / Rust
  -- def_eq_ctx_key): key on the suffix of `types` reachable from
  -- either side; closed pairs (lbr 0) key to the empty context and
  -- share across binder depths. Without the trim, the same pair
  -- compared under every distinct binder context memoizes separately —
  -- on deep dependent proof towers that is an exponential duplicate-
  -- work (and QueryRecord memory) amplifier.
  fn k_is_def_eq(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    match ptr_val(a) - ptr_val(b) {
      0 => 1,  -- ptr-eq: same interned pointer = equal
      _ =>
        let base = lbr_max(expr_lbr(a), expr_lbr(b));
        match base {
          0 => k_is_def_eq_core(a, b, store(ListNode.Nil)),
          _ => k_def_eq_rebase(a, b, types, base),
        },
    }
  }

  -- Rebase an OPEN pair to its minimum loose index before keying.
  -- The prefix trim alone cannot canonicalize a pair that references
  -- only the OUTERMOST binders of a deep telescope: its lbr spans the
  -- whole context, so the trim keeps every inner frame — and each
  -- comparison site spells those (unreferenced) inner frames slightly
  -- differently, minting a fresh memo key per site. Measured on the
  -- mathlib monster: 2.48M distinct (a,b,types) core keys over 15,085
  -- distinct pairs — 164x context multiplicity, the dominant cost.
  --
  -- Fix: `g = min(glb(a), glb(b))` frames at the inner end are loose in
  -- NEITHER side, so lowering both sides by `g` and dropping those
  -- frames is a bijection on derivations (context strengthening by
  -- unreferenced frames — the same argument as the base=0 → Nil arm,
  -- generalized). Def-eq returns a bit, so nothing needs lifting back.
  -- Depth-shifted copies of the same tower also lower to the SAME
  -- hash-consed pair, merging pairs across binder depths, not just
  -- contexts. Kept frames only ever reference deeper (outward) frames,
  -- all of which are kept.
  fn k_def_eq_rebase(a: KExpr, b: KExpr, types: List‹KExpr›,
                         base: G) -> G {
    -- Unconditional: a depth threshold (only rebase past base > 8) was
    -- measured and rejected — it recovered only a third of the overhead
    -- on binder-heavy Init proofs (+6.4% -> +4.2% on Array.append_assoc)
    -- for no gain on the mathlib constant (its full closure was flat,
    -- 8.71e11 vs 8.74e11): not worth a tuning constant.
    let g = lbr_min(lbr_min(expr_glb(a, 0), expr_glb(b, 0)),
                    list_length(types));
    match g {
      0 => k_is_def_eq_core(a, b, ctx_trim(types, base)),
      _ =>
        k_is_def_eq_core(expr_lower(a, g, 0), expr_lower(b, g, 0),
          ctx_trim(list_drop(types, g), base - g)),
    }
  }

  -- Def-eq is symmetric (every tier treats the sides symmetrically or
  -- tries both directions), so canonicalize the pair by pointer order
  -- (mirror k_is_def_eq_core): (a, b) and (b, a) share one ordered
  -- memo row, and the recursion below issues instantiation traffic
  -- with a canonical orientation.
  fn k_is_def_eq_core(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    match u32_less_than(ptr_val(a), ptr_val(b)) {
      1 => k_is_def_eq_ordered(a, b, types),
      _ => k_is_def_eq_ordered(b, a, types),
    }
  }

  fn k_is_def_eq_ordered(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    -- Pre-WHNF lazy-delta app congruence. When both sides share a Const
    -- head, level arguments, and arity, recurse on arguments without
    -- unfolding; otherwise enter the slow path without paying for the
    -- failed congruence attempt in constrained mode.
    -- Soundness: every accepting route reruns a sound def-eq check; choosing
    -- the slow route early can only lose an optimization, not prove equality.
    let route = #k_is_def_eq_ordered_route(a, b, types);
    match route {
      0 => try_def_eq_app(a, b, types),
      1 => k_is_def_eq_slow(a, b, types),
    }
  }

  fn k_is_def_eq_ordered_route(a: KExpr, b: KExpr,
                                    types: List‹KExpr›) -> G {
    match try_def_eq_app(a, b, types) {
      1 => 0,
      _ => 1,
    }
  }

  -- App-congruence PRE-WHNF: if both sides collect_spine to
  -- (Const(addr), args) with same addr + same level args + same arity,
  -- recurse on args pairwise. Sound: if all args def-eq, whole exprs
  -- def-eq without unfolding the const.
  fn try_def_eq_app(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    match collect_spine(a) {
      (ah, aa) =>
        match collect_spine(b) {
          (bh, bb) =>
            match load(ah) {
              KExprNode.Const(a_addr, al) =>
                match load(bh) {
                  KExprNode.Const(b_addr, bl) =>
                    match ptr_val(a_addr) - ptr_val(b_addr) {
                      0 =>
                        match level_list_eq(al, bl) {
                          0 => 0,
                          _ =>
                            match list_length(aa) - list_length(bb) {
                              0 => de_args(aa, bb, types),
                              _ => 0,
                            },
                        },
                      _ => 0,
                    },
                  _ => 0,
                },
              _ => 0,
            },
        },
    }
  }

  fn de_args(aa: List‹KExpr›, bb: List‹KExpr›, types: List‹KExpr›) -> G {
    match load(aa) {
      ListNode.Nil =>
        match load(bb) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(a, ar) =>
        match load(bb) {
          ListNode.Nil => 0,
          ListNode.Cons(b, br) =>
            match k_is_def_eq(a, b, types) {
              0 => 0,
              _ => de_args(ar, br, types),
            },
        },
    }
  }

  -- Nat.zero recognition for offset-aware def_eq.
  fn is_nat_zero(e: KExpr) -> G {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(limbs) => klimbs_is_zero(limbs),
          _ => 0,
        },
      KExprNode.Const(caddr, _) => address_eq(caddr, nat_zero_addr()),
      _ => 0,
    }
  }

  -- Decompose a whnf'd Nat into (matched, base, offset). Recognizes:
  --   Lit n              -> (1, Lit 0, n)
  --   Nat.succ e         -> base/offset of e, offset+1
  --   Nat.add e (Lit m)  -> base/offset of e, offset+m
  -- Mirror nat_offset_of.
  fn nat_offset_of(e: KExpr) -> (G, KExpr, KLimbs) {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(n) => (1, mk_nat_lit(store(ListNode.Nil)), n),
          _ => (0, e, store(ListNode.Nil)),
        },
      KExprNode.App(f, a) =>
        match load(f) {
          KExprNode.Const(caddr, _) =>
            match address_eq(caddr, nat_succ_addr()) {
              1 =>
                match nat_offset_of(a) {
                  (_, base, o) => (1, base, klimbs_succ(o)),
                },
              _ => (0, e, store(ListNode.Nil)),
            },
          KExprNode.App(g, x) =>
            match load(g) {
              KExprNode.Const(caddr, _) =>
                match address_eq(caddr, nat_add_addr()) {
                  1 =>
                    match load(a) {
                      KExprNode.Lit(alit) =>
                        match alit {
                          KLiteral.Nat(m) =>
                            match nat_offset_of(x) {
                              (1, base, o) => (1, base, klimbs_add(o, m)),
                              _ => (1, x, m),
                            },
                          _ => (0, e, store(ListNode.Nil)),
                        },
                      _ => (0, e, store(ListNode.Nil)),
                    },
                  _ => (0, e, store(ListNode.Nil)),
                },
              _ => (0, e, store(ListNode.Nil)),
            },
          _ => (0, e, store(ListNode.Nil)),
        },
      _ => (0, e, store(ListNode.Nil)),
    }
  }

  -- Offset-aware Nat def_eq. Returns (matched, eq). Sound because
  -- `+k` is injective — equal offsets reduces the compare to base ≟ base.
  -- Collapses `succ^k(x) ≟ succ^k(x)` from O(k) unary steps to O(1).
  fn try_def_eq_nat(a: KExpr, b: KExpr, types: List‹KExpr›) -> (G, G) {
    let za = is_nat_zero(a);
    let zb = is_nat_zero(b);
    match za * zb {
      1 => (1, 1),
      _ =>
        match nat_offset_of(a) {
          (ma, ba, oa) =>
            match nat_offset_of(b) {
              (mb, bb, ob) =>
                match ma * mb {
                  0 => (0, 0),
                  _ =>
                    match klimbs_eq(oa, ob) {
                      0 => (0, 0),
                      _ => (1, k_is_def_eq(ba, bb, types)),
                    },
                },
            },
        },
    }
  }

  -- Slow path: whnf both sides, structural compare, then proof-irrel
  -- fallback. On both structural + proof-irrel misses, delta-unfold on
  -- mismatched Const heads is done inside k_is_def_eq_struct via
  -- try_lazy_delta_app.
  -- Tier 1d (mirror DefEq.lean:85-97 / Rust quick_def_eq +
  -- whnf_no_delta_for_def_eq): no-delta whnf both sides; many pairs
  -- settle by ptr-eq, safe structural compare, or app-congruence on
  -- the nd forms — without ever full-delta-unfolding large Defn
  -- bodies. Only on fall-through do we pay Tier 2's full whnf.
  -- Tier 1c (mirror DefEq.lean:78-84 / Rust def_eq.rs:295-304
  -- try_string_lit_expansion): if exactly one side is Lit(Str), expand
  -- it to `String.ofList [Char.ofNat c, ...]` ctor form so both sides
  -- reduce in lockstep through delta + iota instead of the literal
  -- staying opaque while the other side delta-cascades.
  fn try_string_lit_one(t: KExpr, s: KExpr, types: List‹KExpr›) -> G {
    match load(t) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Str(bs) =>
            k_is_def_eq(str_lit_delta_step(str_lit_to_ctor(bs), types),
                           s, types),
          _ => 0,
        },
      _ => 0,
    }
  }

  fn k_is_def_eq_slow(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    -- Soundness: literal routes rerun their def-eq checks, while a dishonest
    -- slow-route hint only defers to the ordinary sound def-eq procedure.
    let route = #k_is_def_eq_slow_route(a, b, types);
    match route {
      0 => try_string_lit_one(a, b, types),
      1 => try_string_lit_one(b, a, types),
      2 => k_is_def_eq_slow_nd(a, b, types),
    }
  }

  fn k_is_def_eq_slow_route(a: KExpr, b: KExpr,
                                 types: List‹KExpr›) -> G {
    match try_string_lit_one(a, b, types) {
      1 => 0,
      _ =>
        match try_string_lit_one(b, a, types) {
          1 => 1,
          _ => 2,
        },
    }
  }

  fn k_is_def_eq_slow_nd(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    let a_core = whnf_struct_core(a, types);
    let b_core = whnf_struct_core(b, types);
    match ptr_val(a_core) - ptr_val(b_core) {
      0 => 1,
      _ =>
        -- Soundness: the selected accepting check is rerun constrained; an
        -- early fallback merely skips a fast path and cannot create equality.
        let route = #k_is_def_eq_slow_nd_route(a_core, b_core, types);
        match route {
          0 => k_is_def_eq_struct_safe(a_core, b_core, types),
          1 => try_def_eq_app(a_core, b_core, types),
          2 => k_is_def_eq_slow_nd_after_core(a, b, a_core, b_core, types),
        },
    }
  }

  fn k_is_def_eq_slow_nd_route(a: KExpr, b: KExpr,
                                    types: List‹KExpr›) -> G {
    match k_is_def_eq_struct_safe(a, b, types) {
      1 => 0,
      _ =>
        match try_def_eq_app(a, b, types) {
          1 => 1,
          _ => 2,
        },
    }
  }

  fn k_is_def_eq_slow_nd_after_core(orig_a: KExpr, orig_b: KExpr,
                                         a: KExpr, b: KExpr,
                                         types: List‹KExpr›) -> G {
    let aw_nd = whnf_nd(a, types);
    let bw_nd = whnf_nd(b, types);
    match ptr_val(aw_nd) - ptr_val(bw_nd) {
      0 => 1,
      _ =>
        -- Soundness: accepting routes rerun sound checks, and selecting the
        -- final fallback early only under-reduces the comparison.
        let route = #k_is_def_eq_slow_nd_after_core_route(aw_nd, bw_nd, types);
        match route {
          0 => k_is_def_eq_struct_safe(aw_nd, bw_nd, types),
          1 => try_def_eq_app(aw_nd, bw_nd, types),
          2 => k_is_def_eq_slow2(orig_a, orig_b, aw_nd, bw_nd, types),
        },
    }
  }

  fn k_is_def_eq_slow_nd_after_core_route(a: KExpr, b: KExpr,
                                               types: List‹KExpr›) -> G {
    match k_is_def_eq_struct_safe(a, b, types) {
      1 => 0,
      _ =>
        match try_def_eq_app(a, b, types) {
          1 => 1,
          _ => 2,
        },
    }
  }

  -- Mirror of Rust `def_eq.rs::quick_def_eq`.
  -- Sound on partially-whnf'd (no-delta) inputs because the handled
  -- shapes (Sort/Lam/Forall) don't depend on further reduction for
  -- their judgment. Returns 1 only when DEFINITELY def-eq; 0 = fall
  -- through.
  fn k_is_def_eq_struct_safe(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    match load(a) {
      KExprNode.Srt(la) =>
        match load(b) {
          KExprNode.Srt(lb) => level_equal(la, lb),
          _ => 0,
        },
      KExprNode.Lam(ty_a, body_a) =>
        match load(b) {
          KExprNode.Lam(ty_b, body_b) =>
            match k_is_def_eq(ty_a, ty_b, types) {
              1 =>
                let inner = store(ListNode.Cons(ty_a, types));
                k_is_def_eq(body_a, body_b, inner),
              _ => 0,
            },
          _ => 0,
        },
      KExprNode.Forall(ty_a, body_a) =>
        match load(b) {
          KExprNode.Forall(ty_b, body_b) =>
            match k_is_def_eq(ty_a, ty_b, types) {
              1 =>
                let inner = store(ListNode.Cons(ty_a, types));
                k_is_def_eq(body_a, body_b, inner),
              _ => 0,
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Tier order is load-bearing: proof_irrel comes BEFORE any
  -- structural/eta machinery. With Thm heads stuck in whnf, proof-term
  -- pairs stay high-level (Lam vs Thm-app etc.); eta-expanding a proof
  -- fabricates over-applied proof terms whose infer_only aborts —
  -- proof_irrel must get first shot.
  -- Takes the no-delta forms slow_nd already computed and NEVER calls
  -- full whnf: full WHNF here would delta-unfold stuck open primitives
  -- such as `Nat.ble` into their recursive logical models and walk
  -- enormous Nat offsets layer by layer (mirror the Tier 4c whnf-core
  -- discipline in crates/kernel/src/def_eq.rs). Delta happens only
  -- inside lazy_delta_loop, one definitional step at a time, with the
  -- cheap tiers re-consulted between steps; the loop hands back its
  -- final forms for the structural fallback tiers.
  fn k_is_def_eq_slow2(orig_a: KExpr, orig_b: KExpr,
                            aw: KExpr, bw: KExpr,
                            types: List‹KExpr›) -> G {
    match ptr_val(aw) - ptr_val(bw) {
      0 => 1,
      _ =>
        -- Soundness: each successful strategy is rerun and asserted.  The
        -- fallback reruns lazy delta to obtain constrained continuation terms.
        let route = #k_is_def_eq_slow2_route(aw, bw, types);
        match route {
          0 =>
            assert_eq!(try_proof_irrel(aw, bw, types), 1);
            1,
          1 =>
            assert_eq!(try_unit_like(aw, bw, types), 1);
            1,
          2 =>
            assert_eq!(try_eta_struct(aw, bw, types), 1);
            1,
          3 =>
            assert_eq!(try_eta_struct(bw, aw, types), 1);
            1,
          4 =>
            let (matched, eq) = try_def_eq_nat(aw, bw, types);
            assert_eq!(matched, 1);
            eq,
          5 =>
            let (matched, _, _) = lazy_delta_loop(aw, bw, 16, types);
            assert_eq!(matched, 1);
            1,
          6 =>
            match lazy_delta_loop(aw, bw, 16, types) {
              (_, fa, fb) => slow2_after_delta(orig_a, orig_b,
                                                fa, fb, types),
            },
        },
    }
  }

  fn k_is_def_eq_slow2_route(aw: KExpr, bw: KExpr,
                                  types: List‹KExpr›) -> G {
    match try_proof_irrel(aw, bw, types) {
      1 => 0,
      _ =>
        match try_unit_like(aw, bw, types) {
          1 => 1,
          _ =>
            match try_eta_struct(aw, bw, types) {
              1 => 2,
              _ =>
                match try_eta_struct(bw, aw, types) {
                  1 => 3,
                  _ =>
                    match try_def_eq_nat(aw, bw, types) {
                      (1, _) => 4,
                      _ =>
                        match lazy_delta_loop(aw, bw, 16, types) {
                          (1, _, _) => 5,
                          _ => 6,
                        },
                    },
                },
            },
        },
    }
  }

  -- Undecided lazy-delta exit. Re-offer the cheap terminal tiers once on
  -- the final forms, but do not restart k_is_def_eq_slow2: doing so refreshes
  -- the lazy budget whenever WHNF rebuilds a term at a fresh pointer and can
  -- turn a bounded projection/constant alternation into an unbounded cycle.
  -- If the accelerator cannot prove equality, restore the historical eager
  -- path on its original inputs.
  fn slow2_after_delta(orig_a: KExpr, orig_b: KExpr,
                            fa: KExpr, fb: KExpr,
                            types: List‹KExpr›) -> G {
    match k_is_def_eq_struct_bounded(fa, fb, 8, types) {
      (1, _) => 1,
      _ => slow2_eager_fallback(orig_a, orig_b, types),
    }
  }

  -- Structural comparison with one credit shared by the entire tree. The
  -- credit permits a single bounded lazy reduction at the first mismatching
  -- subtree; recursive function/argument comparisons thread the remainder,
  -- so work cannot multiply with application depth or sibling count.
  fn k_is_def_eq_struct_bounded(a: KExpr, b: KExpr, credit: G,
                                     types: List‹KExpr›) -> (G, G) {
    match ptr_val(a) - ptr_val(b) {
      0 => (1, credit),
      _ =>
        match load(a) {
          KExprNode.BVar(i) =>
            match load(b) {
              KExprNode.BVar(j) =>
                match i - j { 0 => (1, credit), _ => (0, credit), },
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          KExprNode.Srt(la) =>
            match load(b) {
              KExprNode.Srt(lb) => (level_equal(la, lb), credit),
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          KExprNode.Const(addr_a, lvls_a) =>
            match load(b) {
              KExprNode.Const(addr_b, lvls_b) =>
                match address_eq(addr_a, addr_b) {
                  1 => (level_list_eq(lvls_a, lvls_b), credit),
                  _ => k_is_def_eq_struct_spend(a, b, credit, types),
                },
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          KExprNode.App(fa, xa) =>
            match load(b) {
              KExprNode.App(fb, xb) =>
                match k_is_def_eq_struct_bounded(fa, fb, credit, types) {
                  (1, rest) =>
                    k_is_def_eq_struct_bounded(xa, xb, rest, types),
                  (_, rest) => (0, rest),
                },
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          KExprNode.Lam(ta, ba) =>
            match load(b) {
              KExprNode.Lam(tb, bb) =>
                match k_is_def_eq_struct_bounded(ta, tb, credit, types) {
                  (1, rest) =>
                    let types2 = store(ListNode.Cons(ta, types));
                    k_is_def_eq_struct_bounded(ba, bb, rest, types2),
                  (_, rest) => (0, rest),
                },
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          KExprNode.Forall(ta, ba) =>
            match load(b) {
              KExprNode.Forall(tb, bb) =>
                match k_is_def_eq_struct_bounded(ta, tb, credit, types) {
                  (1, rest) =>
                    let types2 = store(ListNode.Cons(ta, types));
                    k_is_def_eq_struct_bounded(ba, bb, rest, types2),
                  (_, rest) => (0, rest),
                },
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          KExprNode.Lit(la) =>
            match load(b) {
              KExprNode.Lit(lb) => (literal_eq(la, lb), credit),
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          KExprNode.Proj(struct_a, fidx_a, ea) =>
            match load(b) {
              KExprNode.Proj(struct_b, fidx_b, eb) =>
                match address_eq(struct_a, struct_b) {
                  1 =>
                    match fidx_a - fidx_b {
                      0 => k_is_def_eq_struct_bounded(ea, eb, credit, types),
                      _ => (0, credit),
                    },
                  _ => k_is_def_eq_struct_spend(a, b, credit, types),
                },
              _ => k_is_def_eq_struct_spend(a, b, credit, types),
            },
          _ => k_is_def_eq_struct_spend(a, b, credit, types),
        },
    }
  }

  fn k_is_def_eq_struct_spend(a: KExpr, b: KExpr, credit: G,
                                   types: List‹KExpr›) -> (G, G) {
    match credit {
      0 => (0, 0),
      _ =>
        let rest = credit - 1;
        let aw = whnf_nd(a, types);
        let bw = whnf_nd(b, types);
        match ptr_val(aw) - ptr_val(bw) {
          0 => (1, rest),
          _ =>
            -- Soundness: the Nat route asserts its match flag; otherwise the
            -- original lazy-delta path runs and supplies constrained state.
            let route = #struct_spend_nat_route(aw, bw, types);
            match route {
              0 =>
                let (matched, eq) = try_def_eq_nat(aw, bw, types);
                assert_eq!(matched, 1);
                (eq, rest),
              1 =>
                match lazy_delta_loop(aw, bw, 8, types) {
                  (1, _, _) => (1, rest),
                  (_, fa, fb) =>
                    k_is_def_eq_struct_bounded(fa, fb, rest, types),
                },
            },
        },
    }
  }

  fn struct_spend_nat_route(aw: KExpr, bw: KExpr,
                                 types: List‹KExpr›) -> G {
    match try_def_eq_nat(aw, bw, types) {
      (1, _) => 0,
      _ => 1,
    }
  }

  -- Compatibility fallback for pairs the bounded lazy accelerator leaves
  -- undecided. Full WHNF is deliberately applied to the original forms, not
  -- the partially unfolded lazy state, so existing successful reduction
  -- routes remain intact.
  fn slow2_eager_fallback(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    let aw = whnf(a, types);
    let bw = whnf(b, types);
    match ptr_val(aw) - ptr_val(bw) {
      0 => 1,
      _ =>
        -- Soundness: every accepting route reruns an independently sound
        -- equality rule; the final structural comparison remains constrained.
        let route = #slow2_eager_fallback_route(aw, bw, types);
        match route {
          0 => try_proof_irrel(aw, bw, types),
          1 => try_unit_like(aw, bw, types),
          2 => try_eta_struct(aw, bw, types),
          3 => try_eta_struct(bw, aw, types),
          4 =>
            let (matched, eq) = try_def_eq_nat(aw, bw, types);
            assert_eq!(matched, 1);
            eq,
          5 => try_eta_swap(aw, bw, types),
          6 => k_is_def_eq_struct(aw, bw, types),
        },
    }
  }

  -- Prover-side selection for the eager fallback's independent terminal
  -- strategies. The constrained caller repeats exactly the selected
  -- operation; no failed strategy is executed in constrained mode.
  fn slow2_eager_fallback_route(aw: KExpr, bw: KExpr,
                                     types: List‹KExpr›) -> G {
    match try_proof_irrel(aw, bw, types) {
      1 => 0,
      _ =>
        match try_unit_like(aw, bw, types) {
          1 => 1,
          _ =>
            match try_eta_struct(aw, bw, types) {
              1 => 2,
              _ =>
                match try_eta_struct(bw, aw, types) {
                  1 => 3,
                  _ =>
                    match try_def_eq_nat(aw, bw, types) {
                      (1, _) => 4,
                      _ =>
                        match try_eta_swap(aw, bw, types) {
                          1 => 5,
                          _ => 6,
                        },
                    },
                },
            },
        },
    }
  }

  -- Struct-eta: if `s` is a fully-applied ctor of a single-ctor
  -- 0-indices inductive (struct-like) and `t` is any expr,
  -- accept when `Proj(induct, i, t) ≡ s_args[nparams + i]` for every
  -- field. Mirror crates/kernel/src.
  fn try_eta_struct(t: KExpr, s: KExpr, types: List‹KExpr›) -> G {
    match collect_spine(s) {
      (s_head, s_args) =>
        match load(s_head) {
          KExprNode.Const(ctor_addr, _) =>
            let ci = load(get_ci(ctor_addr));
            match ci {
              KConstantInfo.Ctor(_, _, ind_block_addr, ind_idx, _, nparams, nfields, _) =>
                match list_length(s_args) - (nparams + nfields) {
                  0 =>
                    let ind_ci = load(get_ci_iprj(ind_block_addr, ind_idx));
                    match ind_ci {
                      KConstantInfo.Induct(_, _, _, nindices, nctors, _, _, _) =>
                        let shape_ok = eq_zero(nindices) * eq_zero(nctors - 1);
                        match shape_ok {
                          0 => 0,
                          _ =>
                            let struct_addr = compute_iprj_addr(ind_block_addr, ind_idx);
                            -- Eta holds for structure-LIKE inductives only, which
                            -- Lean defines as non-recursive on top of the shape
                            -- test above (`isStructureLike` requires
                            -- `isRec := false`). Firing on a recursive one-ctor
                            -- inductive accepts pairs Lean's kernel rejects. The
                            -- whnf-side struct-eta iota gates on the same
                            -- predicate.
                            match struct_is_rec(struct_addr) {
                              1 => 0,
                              _ =>
                                -- The two sides must have def-eq TYPES.
                                -- Without this the rule degenerates: for
                                -- ANY `t` of ANY type it would compare
                                -- `t` against `S.mk … (Proj S i t) …`,
                                -- and `compare_struct_fields` builds
                                -- exactly those projections, so the
                                -- pointer fast path matches them and the
                                -- pair is accepted. Those projections are
                                -- synthesized inside def-eq and never
                                -- inferred, so `k_infer_proj`'s own
                                -- head-address gate never sees them.
                                -- Mirrors the reference's
                                -- "Types must be def-eq" check
                                -- (crates/kernel/src/def_eq.rs), itself
                                -- lean4lean's `tryEtaStructCore`.
                                let t_ty = k_infer_only(t, types);
                                let s_ty = k_infer_only(s, types);
                                match k_is_def_eq(t_ty, s_ty, types) {
                                  0 => 0,
                                  _ =>
                                    compare_struct_fields(struct_addr, nparams,
                                                               nfields, t, s_args, 0, types),
                                },
                            },
                        },
                      _ => 0,
                    },
                  _ => 0,
                },
              _ => 0,
            },
          _ => 0,
        },
    }
  }

  fn compare_struct_fields(struct_addr: Addr, nparams: G, nfields: G,
                                t: KExpr, s_args: List‹KExpr›, i: G,
                                types: List‹KExpr›) -> G {
    match nfields - i {
      0 => 1,
      _ =>
        let proj_expr = store(KExprNode.Proj(struct_addr, i, t));
        let s_field = list_lookup(s_args, nparams + i);
        match k_is_def_eq(proj_expr, s_field, types) {
          0 => 0,
          _ => compare_struct_fields(struct_addr, nparams, nfields, t,
                                          s_args, i + 1, types),
        },
    }
  }

  -- Synthesize the parent inductive's IPrj wrapper Addr for use as
  -- the struct_addr in Proj nodes. Same recipe as Ingress'
  -- projection_addr but specialized to Indc (no members lookup —
  -- direct Ixon IPrj Constant + blake3).
  fn compute_iprj_addr(block_addr: Addr, idx: G) -> Addr {
    -- Range-check the index rather than truncating it: an unchecked
    -- low-byte pack collides the synthesized wrapper addrs of members
    -- 0 and 256.
    let idx_u64 = idx_to_u64(idx);
    let info = ConstantInfo.IPrj(InductiveProj.Mk(idx_u64, block_addr));
    let proj_c = Constant.Mk(info,
                              store(ListNode.Nil),
                              store(ListNode.Nil),
                              store(ListNode.Nil));
    let bytes = put_constant(proj_c, store(ListNode.Nil));
    bytes_to_addr(bytes)
  }

  -- If exactly one side is a Lam, eta-expand the non-Lam side and retry.
  fn try_eta_swap(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    match load(a) {
      KExprNode.Lam(ta, ba) =>
        match load(b) {
          KExprNode.Lam(_, _) => 0,
          _ => try_eta_expand(ta, ba, b, types),
        },
      _ =>
        match load(b) {
          KExprNode.Lam(tb, bb) => try_eta_expand(tb, bb, a, types),
          _ => 0,
        },
    }
  }

  -- Mirror try_unit_like (Kernel/DefEq.lean:211) / Rust
  -- def_eq.rs:858-905 try_unit_like_eq: if `a`'s type whnfs to
  -- `Const(I, _) args` for a single-ctor zero-field inductive
  -- (PUnit, True, Unit-like structures), any two inhabitants are
  -- definitionally equal — provided `b`'s type is def-eq to `a`'s.
  -- Fires all over brecOn/below machinery (below-package PUnit slots).
  fn try_unit_like(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    let ta = k_infer_only(a, types);
    let ta_w = whnf(ta, types);
    match is_unit_like_type(ta_w) {
      0 => 0,
      _ =>
        let tb = k_infer_only(b, types);
        k_is_def_eq(ta, tb, types),
    }
  }

  -- 1 iff ty is `Const(I, _) args` for a 1-ctor 0-field NON-INDEXED
  -- inductive.
  --
  -- The index count is part of the reference's test (`def_eq.rs:912`,
  -- `if indices != 0 || ctors.len() != 1`) and of lean4lean's
  -- (`numIndices := 0`); it was dropped here, which made `Eq α a b` and
  -- every other 1-ctor 0-field indexed family read as unit-like.
  fn is_unit_like_type(ty: KExpr) -> G {
    match collect_spine(ty) {
      (head, _) =>
        match load(head) {
          KExprNode.Const(addr, _) =>
            let ci = load(get_ci(addr));
            match ci {
              KConstantInfo.Induct(_, _, _, n_indices, num_ctors, _, block, idx) =>
                -- Nested rather than summed: these are field elements, so
                -- `n_indices + (num_ctors - 1)` is zero not only at (0, 1)
                -- but also at (1, 0), where `num_ctors - 1` wraps to p-1.
                match n_indices {
                  0 =>
                    match num_ctors - 1 {
                      0 =>
                        let cci = load(get_ci_cprj(block, idx, 0));
                        match cci {
                          KConstantInfo.Ctor(_, _, _, _, _, _, nfields, _) =>
                            match nfields {
                              0 => 1,
                              _ => 0,
                            },
                          _ => 0,
                        },
                      _ => 0,
                    },
                  _ => 0,
                },
              _ => 0,
            },
          _ => 0,
        },
    }
  }

  -- Mirror crates/kernel/src: if `a`'s type is a Prop,
  -- and `b`'s type is def-eq to `a`'s type, then a ≡ b as proof-terms.
  -- Uses k_infer_only to avoid the def_eq ↔ check cycle.
  fn try_proof_irrel(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    let a_ty = k_infer_only(a, types);
    match is_prop_type(a_ty, types) {
      0 => 0,
      _ =>
        let b_ty = k_infer_only(b, types);
        k_is_def_eq(a_ty, b_ty, types),
    }
  }

  -- `λ ty_a. body_a` vs non-Lam `b` → compare `body_a` against
  -- `App(lift(b, 1, 0), BVar 0)` under the extended context.
  --
  -- `b`'s OWN domain decides whether this is legal, so infer it: all
  -- three references build the wrapper lambda out of `b`'s inferred
  -- binder type, not out of `ty_a`, and the ensuing Lam/Lam comparison
  -- is what checks the two domains agree. Rust `try_eta_expansion`
  -- (`def_eq.rs:1179-1211`) infers `s`, whnfs to `All`, and takes that
  -- `ty`; `Ix/Tc` `tryEtaExpansion` (`DefEq.lean:946-951`) does the same
  -- via `inferOnlyCall`; lean4lean `tryEtaExpansionCore`
  -- (`TypeChecker.lean:507-511`) is `let .forallE name ty _ bi ← whnf
  -- (← inferType s)`.
  --
  -- Reusing `ty_a` and never looking at `b` accepted
  -- `(λ x : A. f x) ≡ f` for any `f`, whatever its domain. Comparing the
  -- domains here is equivalent to the references' route through Lam/Lam,
  -- which compares the domains and then descends under the FIRST
  -- lambda's — hence `ty_a` for the inner context below.
  --
  -- `k_infer_only` to avoid the def-eq ↔ check cycle, as
  -- `try_proof_irrel` does. A non-`Forall` inferred type means eta does
  -- not apply and the ladder falls through to the structural compare,
  -- matching the references' `return false`.
  fn try_eta_expand(ty_a: KExpr, body_a: KExpr, b: KExpr,
                        types: List‹KExpr›) -> G {
    let b_ty = k_infer_only(b, types);
    let b_ty_w = whnf(b_ty, types);
    match load(b_ty_w) {
      KExprNode.Forall(dom_b, _) =>
        match k_is_def_eq(ty_a, dom_b, types) {
          0 => 0,
          _ =>
            let b_lifted = expr_lift(b, 1, 0);
            let bvar0 = store(KExprNode.BVar(0));
            let b_app = store(KExprNode.App(b_lifted, bvar0));
            let inner = store(ListNode.Cons(ty_a, types));
            k_is_def_eq(body_a, b_app, inner),
        },
      _ => 0,
    }
  }

  -- 1 iff `whnf(infer_only(ty))` is `Sort 0`.
  --
  -- STRUCTURAL on purpose — do not swap this for `level_equal`. All three
  -- references gate struct-eta and proof irrelevance on the level being
  -- literally `Zero`: Rust `KUniv::is_zero` (`level.rs:112-114`, a
  -- `matches!` on `UnivData::Zero`), `Ix/Tc` `KUniv.isZero`
  -- (`Level.lean:64-66`), and lean4lean's `isProp`
  -- (`TypeChecker.lean:192-193`), which compares against `.prop` with
  -- structural `==`.
  --
  -- It is sound because levels are built by SIMPLIFYING constructors —
  -- `level_imax` collapses `imax u 0` to `Zero` at construction, as
  -- Rust's `KUniv::imax` and lean4lean's `mkLevelIMax'` do — and because
  -- the test runs after `whnf`. So a Prop cannot reach here spelled any
  -- other way.
  --
  -- Note this is NOT the rule everywhere: the projection-field Prop test
  -- normalizes in Rust (`univ_eq`, `infer.rs:516`) and in `Ix/Tc`
  -- (`Infer.lean:315`), which is why `is_inductive_prop` uses
  -- `level_equal`. Those two tests are deliberately different.
  fn is_prop_type(ty: KExpr, types: List‹KExpr›) -> G {
    let sort = k_infer_only(ty, types);
    let sort_w = whnf(sort, types);
    match load(sort_w) {
      KExprNode.Srt(l) =>
        match load(l) {
          KLevelNode.Zero => 1,
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Structural arm-by-arm equality on WHNF'd exprs. The Lit arm
  -- continues into `k_is_def_eq_struct_go` directly (see there);
  -- keep the two-name split so that call can bypass nothing but the
  -- entry itself.
  fn k_is_def_eq_struct(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    k_is_def_eq_struct_go(a, b, types)
  }

  fn k_is_def_eq_struct_go(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    match load(a) {
      KExprNode.BVar(i) =>
        match load(b) {
          KExprNode.BVar(j) => match i - j { 0 => 1, _ => 0, },
          _ => 0,
        },
      KExprNode.Srt(la) =>
        match load(b) {
          KExprNode.Srt(lb) => level_equal(la, lb),
          _ => 0,
        },
      KExprNode.Const(addr_a, lvls_a) =>
        match load(b) {
          KExprNode.Const(addr_b, lvls_b) =>
            -- Content equality decides which constant this is; pointer
            -- inequality would not (see the `Addr` note in Core.lean).
            match address_eq(addr_a, addr_b) {
              1 => level_list_eq(lvls_a, lvls_b),
              _ => try_lazy_delta_app(a, b, types),
            },
          _ => try_lazy_delta_app(a, b, types),
        },
      KExprNode.App(fa, xa) =>
        match load(b) {
          KExprNode.App(fb, xb) =>
            match k_is_def_eq(fa, fb, types) {
              0 => try_lazy_delta_app(a, b, types),
              _ =>
                match k_is_def_eq(xa, xb, types) {
                  0 => try_lazy_delta_app(a, b, types),
                  _ => 1,
                },
            },
          _ => try_lazy_delta_app(a, b, types),
        },
      KExprNode.Lam(ta, ba) =>
        match load(b) {
          KExprNode.Lam(tb, bb) =>
            match k_is_def_eq(ta, tb, types) {
              0 => 0,
              _ =>
                let types2 = store(ListNode.Cons(ta, types));
                k_is_def_eq(ba, bb, types2),
            },
          _ => try_eta_expand(ta, ba, b, types),
        },
      KExprNode.Forall(ta, ba) =>
        match load(b) {
          KExprNode.Forall(tb, bb) =>
            match k_is_def_eq(ta, tb, types) {
              0 => 0,
              _ =>
                let types2 = store(ListNode.Cons(ta, types));
                k_is_def_eq(ba, bb, types2),
            },
          _ => 0,
        },
      KExprNode.Let(_, _, _) =>
        -- whnf should have zeta-reduced Let already.
        0,
      KExprNode.Lit(la) =>
        match load(b) {
          -- Compare the VALUES, not just the shapes: two Lits are def-eq
          -- only when their payloads are equal. Answering 1 for any pair of
          -- Lits would accept `Lit 5 ≟ Lit 6` and certify `Nat.add 2 3 = 6`.
          -- The earlier def_eq_nat tier handles offset-shaped Nat pairs, but
          -- nothing guarantees it fired before this point, and it never
          -- covers Str.
          KExprNode.Lit(lb) => literal_eq(la, lb),
          _ =>
            -- Lit vs non-Lit: convert `a` to ctor form (Nat.zero /
            -- App(Nat.succ, Lit(k-1))) and retry STRUCTURALLY. Handles
            -- the `Lit(Nat 0) ≡ Const(Nat.zero)` case that comes up
            -- when one side reduces via nat_lit_to_ctor and the other
            -- doesn't ( residual — Nat.pred_le).
            -- MUST NOT re-enter full k_is_def_eq: its whnf collapses
            -- the succ-wrapped form straight back to the same interned
            -- Lit (nat prim), producing an infinite expand/collapse
            -- cycle whenever `b` is a stuck non-ctor app.
            let a_ctor = nat_lit_to_ctor_or_self(a);
            match ptr_val(a_ctor) - ptr_val(a) {
              0 => 0,  -- didn't change, avoid infinite loop
              _ => k_is_def_eq_struct_go(a_ctor, b, types),
            },
        },
      KExprNode.Proj(struct_a, fidx_a, ea) =>
        match load(b) {
          KExprNode.Proj(struct_b, fidx_b, eb) =>
            -- Content equality decides; pointer inequality would not.
            match address_eq(struct_a, struct_b) {
              1 =>
                match fidx_a - fidx_b {
                  0 => k_is_def_eq(ea, eb, types),
                  _ => 0,
                },
              _ => 0,
            },
          _ => 0,
        },
    }
  }

  -- Multi-step lazy-delta reduction loop (mirror Tier 4).
  -- Both sides possibly Const-Defn/Thm-headed. Unfold one side per
  -- iteration (prefer higher-rank/hint), re-normalize with whnf_nd
  -- ONLY — full whnf here would delta-unfold stuck open primitives
  -- (Nat.ble etc.) into their recursive logical models and walk
  -- 2^32-scale offsets — then retry def_eq. Fuel-bounded to prevent
  -- runaway on cyclic unfolds. Returns (1, _, _) when decided equal;
  -- (0, fa, fb) hands the final forms to the caller's structural
  -- fallback tiers.
  fn lazy_delta_loop(a: KExpr, b: KExpr, fuel: G,
                          types: List‹KExpr›) -> (G, KExpr, KExpr) {
    match fuel {
      0 => (0, a, b),
      _ =>
        match ptr_val(a) - ptr_val(b) {
          0 => (1, a, b),
          _ =>
        -- In-loop offset-aware Nat tier: compact `base + K` forms are
        -- decided (either way) without any unfolding.
        -- Soundness: a claimed Nat decision is rerun and asserted.  Skipping
        -- it only continues with sound delta reduction and may false-negative.
        let route = #lazy_delta_nat_route(a, b, types);
        match route {
          0 =>
            let (matched, eq) = try_def_eq_nat(a, b, types);
            assert_eq!(matched, 1);
            (eq, a, b),
          1 =>
        -- Soundness: every claimed Const head is re-extracted and asserted;
        -- treating a Const as non-Const can only take a sound fallback route.
        let head_route = #lazy_delta_head_route(a, b);
        match head_route {
          0 =>
            let (a_addr, a_is_const) = head_addr(a);
            assert_eq!(a_is_const, 1);
            let (b_addr, b_is_const) = head_addr(b);
            assert_eq!(b_is_const, 1);
            -- App congruence already ran before entering lazy delta.
            -- Retrying it here recursively calls full k_is_def_eq for
            -- every argument and resets the lazy budget. Continue the
            -- current bounded reduction instead.
            lazy_delta_step_const_const(a_addr, b_addr, a, b,
                                         fuel, types),
          1 =>
            let (a_addr, a_is_const) = head_addr(a);
            assert_eq!(a_is_const, 1);
            lazy_delta_a_const_b_proj(a_addr, a, b, fuel, types),
          2 =>
            let (b_addr, b_is_const) = head_addr(b);
            assert_eq!(b_is_const, 1);
            lazy_delta_b_const_a_proj(b_addr, a, b, fuel, types),
          3 =>
            -- Neither Const-headed at spine head. Try unfold_proj_app
            -- on both — if either side is Proj-headed with a
            -- delta-eligible inner Const, unfold inner and rewrap.
            lazy_delta_both_proj(a, b, fuel, types),
        },
        },
        },
    }
  }

  fn lazy_delta_nat_route(a: KExpr, b: KExpr,
                               types: List‹KExpr›) -> G {
    match try_def_eq_nat(a, b, types) {
      (1, _) => 0,
      _ => 1,
    }
  }

  fn lazy_delta_head_route(a: KExpr, b: KExpr) -> G {
    let (_, a_is_const) = head_addr(a);
    let (_, b_is_const) = head_addr(b);
    match a_is_const {
      1 =>
        match b_is_const {
          1 => 0,
          _ => 1,
        },
      _ =>
        match b_is_const {
          1 => 2,
          _ => 3,
        },
    }
  }

  -- Reducibility rank for lazy-delta unfold ordering (mirror
  -- delta_rank): Defn carries the ch 3 hint; Thm and everything else
  -- rank 0.
  fn delta_rank(ci: KConstantInfo) -> G {
    match ci {
      KConstantInfo.Defn(_, _, _, _, hint) => hint,
      _ => 0,
    }
  }

  -- Both heads Const, congruence missed. Rank-ordered unfold (mirror
  -- lazy_delta_step_const_const / Rust lazy_delta_reduction_step):
  -- unfold the higher-rank side so both sides meet at the same
  -- definitional height; equal ranks unfold both.
  fn lazy_delta_step_const_const(a_addr: Addr, b_addr: Addr, a: KExpr,
                                       b: KExpr, fuel: G,
                                       types: List‹KExpr›) -> (G, KExpr, KExpr) {
    -- Soundness: each selected delta unfolding is checked by delta_unfold;
    -- a wrong side or no-unfold choice can only fail to establish equality.
    let route = #lazy_delta_const_const_route(a_addr, b_addr);
    match route {
      0 => unfold_a_and_loop(a, b, fuel, types),
      1 => unfold_b_and_loop(a, b, fuel, types),
      2 => unfold_both_and_loop(a, b, fuel, types),
      3 => (0, a, b),
    }
  }

  fn lazy_delta_const_const_route(a_addr: Addr, b_addr: Addr) -> G {
    let a_ci = load(get_ci(a_addr));
    let b_ci = load(get_ci(b_addr));
    let ae = is_defn_or_thm(a_ci);
    let be = is_defn_or_thm(b_ci);
    match ae {
      0 =>
        match be {
          0 => 3,
          _ => 1,
        },
      _ =>
        match be {
          0 => 0,
          _ =>
            let ar = delta_rank(a_ci);
            let br = delta_rank(b_ci);
            match u32_less_than(br, ar) {
              1 => 0,
              _ =>
                match u32_less_than(ar, br) {
                  1 => 1,
                  _ => 2,
                },
            },
        },
    }
  }

  fn unfold_a_and_loop(a: KExpr, b: KExpr, fuel: G,
                           types: List‹KExpr›) -> (G, KExpr, KExpr) {
    match delta_unfold(a) {
      (1, a2) =>
        let aw = whnf_nd(a2, types);
        lazy_delta_loop(aw, b, fuel - 1, types),
      _ => (0, a, b),
    }
  }

  fn unfold_b_and_loop(a: KExpr, b: KExpr, fuel: G,
                           types: List‹KExpr›) -> (G, KExpr, KExpr) {
    match delta_unfold(b) {
      (1, b2) =>
        let bw = whnf_nd(b2, types);
        lazy_delta_loop(a, bw, fuel - 1, types),
      _ => (0, a, b),
    }
  }

  fn unfold_both_and_loop(a: KExpr, b: KExpr, fuel: G,
                              types: List‹KExpr›) -> (G, KExpr, KExpr) {
    match delta_unfold(a) {
      (1, a2) =>
        match delta_unfold(b) {
          (1, b2) =>
            let aw = whnf_nd(a2, types);
            let bw = whnf_nd(b2, types);
            lazy_delta_loop(aw, bw, fuel - 1, types),
          _ => (0, a, b),
        },
      _ => (0, a, b),
    }
  }

  -- a is Const-headed spine; b is Proj-headed. Mirror
  -- lazy_delta_step_a_const: try unfold_proj_app on b, else unfold a.
  fn lazy_delta_a_const_b_proj(a_addr: Addr, a: KExpr, b: KExpr, fuel: G,
                                       types: List‹KExpr›) -> (G, KExpr, KExpr) {
    -- Proj-side unfolding is tried FIRST, independent of whether the
    -- Const side is delta-eligible: under the lazy discipline a
    -- Proj-headed side (e.g. `instLEUInt32.1`) can face a plain
    -- non-Defn head (a ctor-built function constant) and still be one
    -- proj-unfold away from it.
    let a_ci = load(get_ci(a_addr));
    -- Soundness: the consumed projection/Const unfolding is rerun and asserted;
    -- choosing the other sound unfolding only changes reduction order.
    let route = #lazy_delta_const_proj_route(a, a_ci, b, types);
    match route {
      0 =>
        let (matched, b2) = try_unfold_proj_app(b, types);
        assert_eq!(matched, 1);
        lazy_delta_loop(a, b2, fuel - 1, types),
      1 =>
        let (matched, aw) = try_unfold_head(a, a_ci, types);
        assert_eq!(matched, 1);
        lazy_delta_loop(aw, b, fuel - 1, types),
      2 => (0, a, b),
    }
  }

  -- Symmetric.
  fn lazy_delta_b_const_a_proj(b_addr: Addr, a: KExpr, b: KExpr, fuel: G,
                                       types: List‹KExpr›) -> (G, KExpr, KExpr) {
    let b_ci = load(get_ci(b_addr));
    -- Soundness: the consumed projection/Const unfolding is rerun and asserted;
    -- choosing the other sound unfolding only changes reduction order.
    let route = #lazy_delta_const_proj_route(b, b_ci, a, types);
    match route {
      0 =>
        let (matched, a2) = try_unfold_proj_app(a, types);
        assert_eq!(matched, 1);
        lazy_delta_loop(a2, b, fuel - 1, types),
      1 =>
        let (matched, bw) = try_unfold_head(b, b_ci, types);
        assert_eq!(matched, 1);
        lazy_delta_loop(a, bw, fuel - 1, types),
      2 => (0, a, b),
    }
  }

  fn lazy_delta_const_proj_route(const_e: KExpr, const_ci: KConstantInfo,
                                      proj_e: KExpr,
                                      types: List‹KExpr›) -> G {
    match try_unfold_proj_app(proj_e, types) {
      (1, _) => 0,
      _ =>
        match try_unfold_head(const_e, const_ci, types) {
          (1, _) => 1,
          _ => 2,
        },
    }
  }

  -- Both are Proj-headed spines. Try unfold_proj_app on either or both.
  -- Projection/head reductions continue this bounded loop directly.
  -- Re-entering `k_is_def_eq` here would reset the lazy budget on every
  -- step; alternating projection and constant spellings can then recurse
  -- forever (Batteries' Char.toUpper proof cycles around Decidable.casesOn).
  -- The loop itself rechecks ptr/Nat equality, and its caller applies the
  -- remaining structural/eta/full-WHNF tiers to the final forms.
  fn lazy_delta_both_proj(a: KExpr, b: KExpr, fuel: G,
                               types: List‹KExpr›) -> (G, KExpr, KExpr) {
    -- Soundness: every projection result used below is rerun and asserted;
    -- omitting an available unfolding only under-reduces the pair.
    let route = #lazy_delta_both_proj_route(a, b, types);
    match route {
      0 =>
        let (a_matched, a2) = try_unfold_proj_app(a, types);
        assert_eq!(a_matched, 1);
        let (b_matched, b2) = try_unfold_proj_app(b, types);
        assert_eq!(b_matched, 1);
        lazy_delta_loop(a2, b2, fuel - 1, types),
      1 =>
        let (a_matched, a2) = try_unfold_proj_app(a, types);
        assert_eq!(a_matched, 1);
        lazy_delta_loop(a2, b, fuel - 1, types),
      2 =>
        let (b_matched, b2) = try_unfold_proj_app(b, types);
        assert_eq!(b_matched, 1);
        lazy_delta_loop(a, b2, fuel - 1, types),
      3 => (0, a, b),
    }
  }

  fn lazy_delta_both_proj_route(a: KExpr, b: KExpr,
                                     types: List‹KExpr›) -> G {
    match try_unfold_proj_app(a, types) {
      (1, _) =>
        match try_unfold_proj_app(b, types) {
          (1, _) => 0,
          _ => 1,
        },
      _ =>
        match try_unfold_proj_app(b, types) {
          (1, _) => 2,
          _ => 3,
        },
    }
  }

  fn is_defn_or_thm(ci: KConstantInfo) -> G {
    match ci {
      KConstantInfo.Defn(_, _, _, _, _) => 1,
      KConstantInfo.Thm(_, _, _) => 1,
      _ => 0,
    }
  }

  -- First reduce the whole projection-headed spine without delta, so cheap
  -- projection/iota and primitive rules fire before we expose dictionary
  -- implementations. Aiur WHNF may rebuild an unchanged stuck expression at
  -- a fresh pointer (unlike Rust's hash-consed expressions), so real progress
  -- means that the projection head disappeared. If it remains stuck, retain
  -- the old single delta step on its scrutinee: signed-integer proofs need to
  -- expose a ctor-built instance before the projection can fire. Continuing
  -- the caller's bounded lazy loop prevents either path from resetting fuel.
  fn try_unfold_proj_app(e: KExpr, types: List‹KExpr›) -> (G, KExpr) {
    match collect_spine(e) {
      (head, spine) =>
        match load(head) {
          KExprNode.Proj(struct_addr, fidx, inner) =>
            let reduced = whnf_nd(e, types);
            match collect_spine(reduced) {
              (reduced_head, _) =>
                match load(reduced_head) {
                  KExprNode.Proj(_, _, _) =>
                    match delta_unfold(inner) {
                      (1, inner2) =>
                        let new_head = store(KExprNode.Proj(struct_addr, fidx, inner2));
                        (1, apply_spine(new_head, spine)),
                      _ => (0, e),
                    },
                  _ => (1, reduced),
                },
            },
          _ => (0, e),
        },
    }
  }

  -- Delta-unfold Const-headed e: replace Const with its Defn/Thm body,
  -- keeping the spine. Returns (0, e) if head isn't Const-Defn/Thm.
  fn delta_unfold(e: KExpr) -> (G, KExpr) {
    match collect_spine(e) {
      (head, spine) =>
        match load(head) {
          KExprNode.Const(addr, lvls) =>
            let ci = load(get_ci(addr));
            match ci {
              KConstantInfo.Defn(_, _, value, _, _) =>
                let body = expr_inst_levels(value, lvls);
                (1, apply_spine(body, spine)),
              KConstantInfo.Thm(_, _, value) =>
                let body = expr_inst_levels(value, lvls);
                (1, apply_spine(body, spine)),
              _ => (0, e),
            },
          _ => (0, e),
        },
    }
  }

  -- Lazy delta: unfold Defn on one side (prefer whichever has body),
  -- retry. On stuck (neither is Defn), give up.
  fn try_lazy_delta_app(a: KExpr, b: KExpr, types: List‹KExpr›) -> G {
    let (a_addr, a_is_const) = head_addr(a);
    let (b_addr, b_is_const) = head_addr(b);
    match a_is_const {
      0 => 0,
      _ =>
        match b_is_const {
          0 => 0,
          _ =>
            let a_ci = load(get_ci(a_addr));
            let b_ci = load(get_ci(b_addr));
            -- Soundness: each unfolded term consumed below is rerun and
            -- asserted; selecting fewer unfoldings can only false-negative.
            let route = #try_lazy_delta_app_route(a, b, a_ci, b_ci, types);
            match route {
              0 =>
                let (a_matched, aw) = try_unfold_head(a, a_ci, types);
                assert_eq!(a_matched, 1);
                let (b_matched, bw) = try_unfold_head(b, b_ci, types);
                assert_eq!(b_matched, 1);
                k_is_def_eq(aw, bw, types),
              1 =>
                let (a_matched, aw) = try_unfold_head(a, a_ci, types);
                assert_eq!(a_matched, 1);
                k_is_def_eq(aw, b, types),
              2 =>
                let (b_matched, bw) = try_unfold_head(b, b_ci, types);
                assert_eq!(b_matched, 1);
                k_is_def_eq(a, bw, types),
              3 => 0,
            },
        },
    }
  }

  fn try_lazy_delta_app_route(a: KExpr, b: KExpr,
                                   a_ci: KConstantInfo,
                                   b_ci: KConstantInfo,
                                   types: List‹KExpr›) -> G {
    match try_unfold_head(a, a_ci, types) {
      (1, _) =>
        match try_unfold_head(b, b_ci, types) {
          (1, _) => 0,
          _ => 1,
        },
      _ =>
        match try_unfold_head(b, b_ci, types) {
          (1, _) => 2,
          _ => 3,
        },
    }
  }

  -- Extract Const head's addr from a spine expr. Returns (addr, is_const).
  fn head_addr(e: KExpr) -> (Addr, G) {
    match collect_spine(e) {
      (head, _) =>
        match load(head) {
          KExprNode.Const(addr, _) => (addr, 1),
          _ => (store([0u8; 32]), 0),
        },
    }
  }

  -- If ci is a Defn or Thm, delta-unfold its body, reapply the spine,
  -- and whnf. Thm must go through delta_unfold explicitly — whnf
  -- keeps Thm heads stuck (mirror), so `whnf(e)` alone would
  -- return `e` unchanged for Thm and stall the lazy-delta loop.
  fn try_unfold_head(e: KExpr, ci: KConstantInfo,
                         types: List‹KExpr›) -> (G, KExpr) {
    match ci {
      -- Defn must ALSO go through the explicit delta_unfold, not
      -- `whnf(e)`: offset-stuck compact forms (`Nat.add/div/mod base
      -- lit`, whnf verdict 2) are whnf-FIXPOINTS, so "unfold via whnf"
      -- returns the same pointer and the lazy-delta ladder recurses on
      -- identical args forever. Explicit body substitution guarantees
      -- progress (mirror delta_unfold).
      KConstantInfo.Defn(_, _, _, _, _) =>
        match delta_unfold(e) {
          (1, e2) => (1, whnf_nd(e2, types)),
          _ => (0, e),
        },
      KConstantInfo.Thm(_, _, _) =>
        match delta_unfold(e) {
          (1, e2) => (1, whnf_nd(e2, types)),
          _ => (0, e),
        },
      _ => (0, e),
    }
  }
⟧

end IxVM

end
