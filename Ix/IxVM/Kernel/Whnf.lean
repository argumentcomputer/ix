module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Levels
public import Ix.IxVM.Kernel.Primitive

public section

namespace IxVM

/-! ## Weak Head Normal Form over `KExpr`

Mirrors `src/ix/kernel/whnf.rs`.

Reduces an expression to head-canonical form. The head after WHNF is one of:

* `Sort(level)` — universe.
* `Lam(ty, body)` — function value.
* `Forall(ty, body)` — function type.
* `Const(idx, lvls)` applied to args where the constant is non-reducible
  (Axiom, Indc, Ctor, Recr stuck on non-Ctor major).
* `BVar(i)` applied to args (open term).
* `Let(...)` — never (always reduces via zeta).
* `Lit(...)` — already a value.
* `Proj(...)` stuck on non-Ctor.

This file implements the essential phases:

1. **delta**: `Const(idx)` where the constant is `Defn` or `Thm` →
   unfold value, instantiate level params, reapply spine, recurse.
2. **beta**: `App(Lam(_, body), arg)` → `body[BVar(0) := arg]`, recurse.
3. **zeta**: `Let(_, val, body)` → `body[BVar(0) := val]`, recurse.
4. **proj**: `Proj(tidx, fidx, e)` where `e` reduces to a `Ctor` →
   pull field via the ctor's spine, recurse.
5. **iota**: `Const(Recr) spine` where `spine[major_idx]` reduces to a
   `Ctor` → look up rule by ctor's `cidx`, instantiate RHS with rec
   levels, apply the params/motives/minors prefix of the spine, then
   ctor's tail fields, then post-major spine; recurse.
6. **nat-prim** (`prims` argument): when `Const(idx)` head matches a
   primitive Nat op slot in `prims` and the spine carries `Lit(Nat(_))`
   args, fold to the literal result.

Constants resolve lazily by reference via `get_ci` (`Ingress.lean`);
primitive dispatch compares the head's address (`cref_std_addr`) against
hardcoded primitive addresses.
-/

def whnf := ⟦
  fn apply_spine(head: KExpr, spine: List‹KExpr›) -> KExpr {
    match load(spine) {
      ListNode.Nil => head,
      ListNode.Cons(a, rest) =>
        apply_spine(store(KExprNode.App(head, a)), rest),
    }
  }

  -- ============================================================================
  -- Beta
  --
  -- One argument per step, NOT a simultaneous multi-arg substitution: a
  -- measured choice. A simultaneous `instantiate_rev`-style peel was
  -- tried (2026-06-10) and REGRESSED FFT ~3%: recursor betas share a
  -- constant argument prefix across iterations (motive/base/step), so
  -- the sequential chain's per-arg memo keys hit across every iteration,
  -- while a combined args-list key is unique per iteration and re-walks
  -- the whole body each time. Curried beats tupled under Aiur's
  -- content-memoization.
  -- ============================================================================

  -- Peel a beta telescope: consume one spine arg per leading `Lam` of `lam`,
  -- accumulating the consumed args innermost-first in `acc` (prepend), until
  -- the head is no longer a `Lam` or the spine is empty. Returns the deepest
  -- body, the consumed args (innermost-first, ready for `expr_inst_many`), and
  -- the unconsumed spine tail.
  fn peel_beta(lam: KExpr, spine: List‹KExpr›, acc: List‹KExpr›)
              -> (KExpr, List‹KExpr›, List‹KExpr›) {
    match load(lam) {
      KExprNode.Lam(_, body) =>
        match load(spine) {
          ListNode.Cons(a, rest) =>
            peel_beta(body, rest, store(ListNode.Cons(a, acc))),
          ListNode.Nil => (lam, acc, spine),
        },
      _ => (lam, acc, spine),
    }
  }

  -- ============================================================================
  -- WHNF main loop with `prims` for nat-primitive dispatch.
  -- ============================================================================

  -- Multi-arg beta (mirror src/ix/kernel/whnf.rs:541-567): peel the whole
  -- telescope and substitute all consumed args in ONE `expr_inst_many` walk,
  -- instead of one `expr_inst1` re-walk of the body per arg. Single-arg betas
  -- stay on the cheap `expr_inst1` path (no list overhead).
  fn whnf_apply_beta(spine: List‹KExpr›, lam: KExpr, types: List‹KExpr›) -> KExpr {
    match peel_beta(lam, spine, store(ListNode.Nil)) {
      (deep, consumed, rest) =>
        match list_length(consumed) {
          0 => apply_spine(lam, spine),
          1 =>
            let body2 = expr_inst1(deep, list_lookup(consumed, 0), 0);
            whnf_with_spine(body2, rest, types),
          _ =>
            let body2 = expr_inst_many(deep, consumed, 0);
            whnf_with_spine(body2, rest, types),
        },
    }
  }

  fn whnf_with_spine(head: KExpr, spine: List‹KExpr›, types: List‹KExpr›) -> KExpr {
    match load(head) {
      KExprNode.App(f, a) =>
        -- Head is itself App-spine (post-beta result). Collect its spine
        -- and prepend to the outer spine, then recurse. Without this,
        -- post-delta beta-reduced bodies like `Nat.rec PUnit step n`
        -- stay stuck and iota never fires.
        match collect_spine(head) {
          (inner_head, inner_spine) =>
            whnf_with_spine(inner_head, list_concat(inner_spine, spine), types),
        },
      KExprNode.Lam(ty, body) =>
        whnf_apply_beta(spine, head, types),
      KExprNode.Const(idx, lvls) =>
        -- Const-head reduction (delta / iota / quot / primitive dispatch) is the
        -- widest arm by far. Factored into `whnf_const_head` so `whnf_with_spine`
        -- stays narrow for the ~76% of reduction steps that are App/Lam/Proj —
        -- Aiur charges a function's full width on every row, so the wide dispatch
        -- only taxes the Const-head rows in its own circuit.
        whnf_const_head(idx, lvls, head, spine, types),
      KExprNode.Let(_, val, body) =>
        let next = expr_inst1(body, val, 0);
        whnf_with_spine(next, spine, types),
      KExprNode.Proj(tidx, fidx, inner) =>
        -- Proj reduction (whnf the scrutinee, fin-val rewrite, ctor field pull)
        -- is the next-widest arm. Factored out for the same reason as Const.
        whnf_proj_head(tidx, fidx, inner, spine, types),
      _ => apply_spine(head, spine),
    }
  }

  -- Proj-head WHNF dispatch, split out of `whnf_with_spine` (see its Proj arm).
  fn whnf_proj_head(tidx: CRef, fidx: G, inner: KExpr, spine: List‹KExpr›,
                    types: List‹KExpr›) -> KExpr {
    let inner_whnf = whnf(inner, types);
    let inner_pair = collect_spine(inner_whnf);
    match inner_pair {
      (inner_head, inner_args) =>
        -- Mirror: whnf.rs:1441-1500 try_reduce_fin_val_decidable_rec.
        -- Pushes Fin.val inside Decidable.rec minors; allows iota.
        let fvd_pair = try_reduce_fin_val_decidable_rec(tidx, fidx, inner_head, inner_args);
        match fvd_pair {
          (1, rewritten) => whnf_with_spine(rewritten, spine, types),
          (0, _) =>
            match load(inner_head) {
              KExprNode.Const(cidx, _) =>
                let cci = load(get_ci(cidx));
                match cci {
                  KConstantInfo.Ctor(_, _, _, _, nparams, _, _) =>
                    let field = list_lookup_or_nil(inner_args, nparams + fidx);
                    whnf_with_spine(field, spine, types),
                  _ =>
                    let stuck = store(KExprNode.Proj(tidx, fidx, inner_whnf));
                    apply_spine(stuck, spine),
                },
              _ =>
                let stuck = store(KExprNode.Proj(tidx, fidx, inner_whnf));
                apply_spine(stuck, spine),
            },
        },
    }
  }

  -- Const-head WHNF dispatch, split out of `whnf_with_spine` (see its Const arm).
  -- `head` is the original `Const(idx, lvls)` KExpr, passed for the stuck
  -- `apply_spine(head, spine)` fallbacks.
  fn whnf_const_head(idx: CRef, lvls: List‹KLevel›, head: KExpr, spine: List‹KExpr›,
                     types: List‹KExpr›) -> KExpr {
    let head_addr = cref_std_addr(idx);
    let ci = load(get_ci(idx));
    -- Recr / Quot heads can never match a primitive address (Nat ops,
    -- Str ops, BitVec, native, decidable, proj-def all live as Ctor or
    -- Defn). Skip the primitive dispatch chain for those.
    match ci {
      KConstantInfo.Rec(num_lvls, _, num_params, num_indices, num_motives, num_minors, rules, k_flag, _, _) =>
        let iota = try_iota(lvls, spine, num_lvls, num_params, num_indices, num_motives, num_minors, rules, k_flag, types);
        match iota {
          (1, reduced2) => whnf(reduced2, types),
          (0, _) => apply_spine(head, spine),
        },
      KConstantInfo.Quot(_, _, kind) =>
        let qiota = try_quot_iota(kind, spine, types);
        match qiota {
          (1, reduced_q) => whnf(reduced_q, types),
          (0, _) => apply_spine(head, spine),
        },
      _ =>
        -- Family-gated primitive dispatch. `prim_family` is keyed on the
        -- head ADDRESS alone, so it memoizes to one row per distinct
        -- constant address in the run; at most ONE family reducer is
        -- then called. The previous form ran every reducer as a gauntlet
        -- (nat -> str -> bitvec -> native -> decidable), charging 4-6
        -- wide rows per Const-head whnf for guaranteed misses — the
        -- families' address sets are mutually disjoint, so the gauntlet
        -- order never mattered. A family-reducer miss (e.g. `Nat.add` on
        -- non-literal args) falls through to proj-def/delta exactly as
        -- the gauntlet's final arm did.
        let fam = prim_family(head_addr);
        let attempt = match fam {
          1 => try_nat_dispatch(head_addr, spine, types),
          2 => try_str_dispatch(head_addr, spine),
          3 => try_bitvec_dispatch(head_addr, spine, types),
          4 => try_reduce_native(head_addr, spine, types),
          5 => try_reduce_decidable(head_addr, idx, lvls, spine, types),
          _ => (0, store(KExprNode.BVar(0))),
        };
        match attempt {
          (1, reduced) => whnf(reduced, types),
          -- verdict 2: the reducer normalized the term to an already-stuck
          -- compact form (symbolic Nat offset); return it WITHOUT re-whnf,
          -- which would loop.
          (2, stuck) => stuck,
          (0, _) =>
            let proj_def_pair = try_reduce_projection_definition(idx, spine);
            match proj_def_pair {
              (1, reduced_pd) => whnf(reduced_pd, types),
              (0, _) =>
                -- Mirror src/ix/kernel/whnf.rs:756-774
                -- (`delta_unfold_one`): unfold any Defn
                -- regardless of `ReducibilityHints`. The
                -- hint is consulted by lazy-delta's
                -- `delta_rank` for def-eq priority, not
                -- as a gate on plain whnf delta. Without
                -- unfolding here, ctor field types
                -- written via opaque defs (e.g.
                -- `constType (n α) (n α)`) stay stuck
                -- and `check_positivity_aug` misclassifies.
                match ci {
                  KConstantInfo.Defn(_, _, value, _, _) =>
                    let body = expr_inst_levels(value, lvls);
                    whnf_with_spine(body, spine, types),
                  KConstantInfo.Thm(_, _, _) => apply_spine(head, spine),
                  _ => apply_spine(head, spine),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- whnf_nd: WHNF without delta-unfolding (`src/ix/kernel/whnf.rs::whnf_no_delta`).
  --
  -- Same dispatch tree as `whnf`, but `whnf_nd_const_head`'s `Defn` arm
  -- returns the stuck application instead of unfolding. Beta / let zeta /
  -- iota / proj / quot / primitives still fire — they don't require delta.
  --
  -- Used by def_eq's Tier 1d structural pre-check (Rust def_eq.rs:320-326):
  -- many comparisons settle at no-delta whnf + ptr_eq or structural quick
  -- comparison, avoiding the cascading delta-unfold work.
  -- ============================================================================
  fn whnf_nd(e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.Srt(_) => e,
      KExprNode.Lit(_) => e,
      KExprNode.Lam(_, _) => e,
      KExprNode.Forall(_, _) => e,
      KExprNode.BVar(_) => e,
      _ => whnf_nd_core(e, ctx_trim(types, expr_lbr(e))),
    }
  }

  fn whnf_nd_core(e: KExpr, types: List‹KExpr›) -> KExpr {
    let pair = collect_spine(e);
    match pair {
      (head, spine) => whnf_nd_with_spine(head, spine, types),
    }
  }

  fn whnf_nd_with_spine(head: KExpr, spine: List‹KExpr›, types: List‹KExpr›) -> KExpr {
    match load(head) {
      KExprNode.App(f, a) =>
        match collect_spine(head) {
          (inner_head, inner_spine) =>
            whnf_nd_with_spine(inner_head, list_concat(inner_spine, spine), types),
        },
      KExprNode.Lam(ty, body) =>
        whnf_nd_apply_beta(spine, head, types),
      KExprNode.Const(idx, lvls) =>
        whnf_nd_const_head(idx, lvls, head, spine, types),
      KExprNode.Let(_, val, body) =>
        let next = expr_inst1(body, val, 0);
        whnf_nd_with_spine(next, spine, types),
      KExprNode.Proj(tidx, fidx, inner) =>
        whnf_nd_proj_head(tidx, fidx, inner, spine, types),
      _ => apply_spine(head, spine),
    }
  }

  fn whnf_nd_apply_beta(spine: List‹KExpr›, lam: KExpr, types: List‹KExpr›) -> KExpr {
    match peel_beta(lam, spine, store(ListNode.Nil)) {
      (deep, consumed, rest) =>
        match list_length(consumed) {
          0 => apply_spine(lam, spine),
          1 =>
            let body2 = expr_inst1(deep, list_lookup(consumed, 0), 0);
            whnf_nd_with_spine(body2, rest, types),
          _ =>
            let body2 = expr_inst_many(deep, consumed, 0);
            whnf_nd_with_spine(body2, rest, types),
        },
    }
  }

  fn whnf_nd_proj_head(tidx: CRef, fidx: G, inner: KExpr, spine: List‹KExpr›,
                        types: List‹KExpr›) -> KExpr {
    let inner_whnf = whnf_nd(inner, types);
    let inner_pair = collect_spine(inner_whnf);
    match inner_pair {
      (inner_head, inner_args) =>
        let fvd_pair = try_reduce_fin_val_decidable_rec(tidx, fidx, inner_head, inner_args);
        match fvd_pair {
          (1, rewritten) => whnf_nd_with_spine(rewritten, spine, types),
          (0, _) =>
            match load(inner_head) {
              KExprNode.Const(cidx, _) =>
                let cci = load(get_ci(cidx));
                match cci {
                  KConstantInfo.Ctor(_, _, _, _, nparams, _, _) =>
                    let field = list_lookup_or_nil(inner_args, nparams + fidx);
                    whnf_nd_with_spine(field, spine, types),
                  _ =>
                    let stuck = store(KExprNode.Proj(tidx, fidx, inner_whnf));
                    apply_spine(stuck, spine),
                },
              _ =>
                let stuck = store(KExprNode.Proj(tidx, fidx, inner_whnf));
                apply_spine(stuck, spine),
            },
        },
    }
  }

  -- The difference from `whnf_const_head`: Defn arm returns stuck instead of
  -- unfolding. Iota, quot, primitives, proj-defs still apply.
  fn whnf_nd_const_head(idx: CRef, lvls: List‹KLevel›, head: KExpr, spine: List‹KExpr›,
                         types: List‹KExpr›) -> KExpr {
    let head_addr = cref_std_addr(idx);
    let ci = load(get_ci(idx));
    match ci {
      KConstantInfo.Rec(num_lvls, _, num_params, num_indices, num_motives, num_minors, rules, k_flag, _, _) =>
        let iota = try_iota(lvls, spine, num_lvls, num_params, num_indices, num_motives, num_minors, rules, k_flag, types);
        match iota {
          (1, reduced2) => whnf_nd(reduced2, types),
          (0, _) => apply_spine(head, spine),
        },
      KConstantInfo.Quot(_, _, kind) =>
        let qiota = try_quot_iota(kind, spine, types);
        match qiota {
          (1, reduced_q) => whnf_nd(reduced_q, types),
          (0, _) => apply_spine(head, spine),
        },
      _ =>
        -- Family-gated primitive dispatch, same as `whnf_const_head`.
        let fam = prim_family(head_addr);
        let attempt = match fam {
          1 => try_nat_dispatch(head_addr, spine, types),
          2 => try_str_dispatch(head_addr, spine),
          3 => try_bitvec_dispatch(head_addr, spine, types),
          4 => try_reduce_native(head_addr, spine, types),
          5 => try_reduce_decidable(head_addr, idx, lvls, spine, types),
          _ => (0, store(KExprNode.BVar(0))),
        };
        match attempt {
          (1, reduced) => whnf_nd(reduced, types),
          -- verdict 2: already-stuck compact form; do not re-whnf.
          (2, stuck) => stuck,
          (0, _) =>
            let proj_def_pair = try_reduce_projection_definition(idx, spine);
            match proj_def_pair {
              (1, reduced_pd) => whnf_nd(reduced_pd, types),
              (0, _) =>
                -- Defn / Thm / etc.: STUCK in no-delta mode. The whole point.
                apply_spine(head, spine),
            },
        },
    }
  }

  -- No fuel limit (unlike Rust's `MAX_WHNF_FUEL = 10_000` in
  -- `src/ix/kernel/tc.rs`). In a zk prover context, divergent input simply
  -- fails to produce a proof — the caller guarantees termination, so a
  -- soundness-preserving early abort is unnecessary.
  fn whnf(e: KExpr, types: List‹KExpr›) -> KExpr {
    -- Fast path: trivial whnf normal forms. Srt / Lit / Lam / Forall / BVar
    -- never reduce — skip collect_spine + dispatch (and the context trim).
    match load(e) {
      KExprNode.Srt(_) => e,
      KExprNode.Lit(_) => e,
      KExprNode.Lam(_, _) => e,
      KExprNode.Forall(_, _) => e,
      KExprNode.BVar(_) => e,
      -- Context-trimmed memo key (mirror Rust `whnf_key`): reduce on the
      -- reachable suffix so a closed term shares its WHNF across binder depths.
      _ => whnf_core(e, ctx_trim(types, expr_lbr(e))),
    }
  }

  fn whnf_core(e: KExpr, types: List‹KExpr›) -> KExpr {
    let pair = collect_spine(e);
    match pair {
      (head, spine) => whnf_with_spine(head, spine, types),
    }
  }

  -- ============================================================================
  -- Iota (recursor on ctor)
  -- ============================================================================
  fn try_iota(lvls: List‹KLevel›, spine: List‹KExpr›,
              num_lvls: G, num_params: G, num_indices: G,
              num_motives: G, num_minors: G,
              rules: List‹KRecRule›, k_flag: G, types: List‹KExpr›) -> (G, KExpr) {
    let major_idx = num_params + num_motives + num_minors + num_indices;
    let spine_len = list_length(spine);
    let major_lt = u32_less_than(major_idx, spine_len);
    match major_lt {
      0 => (0, store(KExprNode.BVar(0))),
      1 =>
        let lvls_len = list_length(lvls);
        match lvls_len - num_lvls {
          0 =>
            try_iota_with_major(lvls, spine, num_params, num_motives, num_minors,
                                major_idx, rules, k_flag, types),
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- Mirror src/ix/kernel/whnf.rs:1113-1143 cleanup_nat_offset_major.
  -- If `e` is `Nat.add base lit` with lit > 0, return one-layer-exposed
  -- `Nat.succ pred` where pred = base if lit == 1, else `Nat.add base (lit-1)`.
  -- Else returns `e` unchanged. Skips Nat literals (already evaluable).
  fn cleanup_nat_offset_major(e: KExpr) -> KExpr {
    match load(e) {
      KExprNode.Lit(_) => e,
      _ =>
        match collect_spine(e) {
          (head, args) =>
            match load(head) {
              KExprNode.Const(_, _) =>
                match try_match_nat_add(head, args) {
                  (1, base, lit) =>
                    let lit_norm = klimbs_normalize(lit);
                    match klimbs_is_zero(lit_norm) {
                      1 => e,
                      0 => build_succ_offset(base, lit_norm),
                    },
                  _ => e,
                },
              _ => e,
            },
        },
    }
  }

  -- If head is Const(nat_add) and args has length 2 and args[1] is Lit Nat,
  -- return (1, base, limbs). Else (0, _, _).
  fn try_match_nat_add(head: KExpr, args: List‹KExpr›) -> (G, KExpr, KLimbs) {
    match load(head) {
      KExprNode.Const(idx, _) =>
        let head_addr = cref_std_addr(idx);
        match address_eq(head_addr, nat_add_addr()) {
          0 => (0, head, store(ListNode.Nil)),
          1 =>
            match list_length(args) - 2 {
              0 =>
                let lhs = list_lookup(args, 0);
                let rhs = list_lookup(args, 1);
                match load(rhs) {
                  KExprNode.Lit(lit) =>
                    match lit {
                      KLiteral.Nat(limbs) => (1, lhs, limbs),
                      _ => (0, head, store(ListNode.Nil)),
                    },
                  _ => (0, head, store(ListNode.Nil)),
                },
              _ => (0, head, store(ListNode.Nil)),
            },
        },
      _ => (0, head, store(ListNode.Nil)),
    }
  }

  -- Build `Nat.succ pred` where pred = base if lit==1, else `Nat.add base (lit-1)`.
  fn build_succ_offset(base: KExpr, lit: KLimbs) -> KExpr {
    let one = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    let lit_minus_one = klimbs_sub(lit, one);
    let pred_lit_norm = klimbs_normalize(lit_minus_one);
    let succ_const = mk_prim_const(nat_succ_addr());
    match klimbs_is_zero(pred_lit_norm) {
      1 => store(KExprNode.App(succ_const, base)),
      0 =>
        let pred_lit_expr = store(KExprNode.Lit(KLiteral.Nat(pred_lit_norm)));
        let pred = store(KExprNode.App(
          store(KExprNode.App(mk_prim_const(nat_add_addr()), base)),
          pred_lit_expr));
        store(KExprNode.App(succ_const, pred)),
    }
  }

  fn try_iota_with_major(lvls: List‹KLevel›, spine: List‹KExpr›,
                         num_params: G, num_motives: G, num_minors: G,
                         major_idx: G, rules: List‹KRecRule›, k_flag: G,
                         types: List‹KExpr›) -> (G, KExpr) {
    -- Mirror: src/ix/kernel/whnf.rs:1824-1869 try_reduce_nat_succ_linear_rec.
    -- Fast path: `Nat.rec _ base (λ _ ih => succ ih) (Lit n)` → `base + n`.
    -- O(1) instead of O(n) iota expansion of literal succ chain.
    let lin = try_nat_linear_rec(spine, num_params, num_motives, num_minors,
                                  major_idx, types);
    match lin {
      (1, r) => (1, r),
      (0, _) =>
    let raw_major = list_lookup(spine, major_idx);
    -- K-target shortcut: when recursor's k_flag is set, attempt to
    -- synthesize a nullary ctor application from the spine's params,
    -- enabling iota even when the major isn't reduced to a Ctor.
    -- Mirror: src/ix/kernel/whnf.rs:1315-1380 synth_ctor_when_k.
    let major = match k_flag {
      1 =>
        let synth = try_synth_k_ctor(raw_major, num_params, rules,
                                     types);
        match synth {
          (1, ctor_app) => ctor_app,
          (0, _) => raw_major,
        },
      0 => raw_major,
    };
    -- Pre-WHNF cleanup: if major is `Nat.add base lit` with lit > 0, expose
    -- one Nat.succ layer to enable iota without unfolding Nat.add into a
    -- chain of `lit` intermediate literals. Mirror whnf.rs:904-907,1113-1143
    -- cleanup_nat_offset_major.
    let major_clean1 = cleanup_nat_offset_major(major);
    let major_whnf_raw = whnf(major_clean1, types);
    let major_clean2 = cleanup_nat_offset_major(major_whnf_raw);
    -- Coerce Nat / Str literals to ctor chain so iota fires
    -- (mirror whnf.rs:929-946 nat, whnf.rs:953-960 string).
    let major_whnf_nat = nat_lit_to_ctor_or_self(major_clean2);
    let major_whnf = str_lit_to_ctor_or_self(major_whnf_nat);
    let major_pair = collect_spine(major_whnf);
    match major_pair {
      (ctor_head, ctor_args) =>
        match load(ctor_head) {
          KExprNode.Const(ctor_idx, _) =>
            let ctor_ci = load(get_ci(ctor_idx));
            match ctor_ci {
              KConstantInfo.Ctor(_, _, _, cidx, _, ctor_nfields, _) =>
                let rules_len = list_length(rules);
                let cidx_in_range = u32_less_than(cidx, rules_len);
                match cidx_in_range {
                  0 => (0, store(KExprNode.BVar(0))),
                  1 =>
                    let ctor_args_len = list_length(ctor_args);
                    let too_few_fields = u32_less_than(ctor_args_len, ctor_nfields);
                    match too_few_fields {
                      1 => (0, store(KExprNode.BVar(0))),
                      0 =>
                        let rule = list_lookup(rules, cidx);
                        match rule {
                          KRecRule.Mk(_, _, rhs) =>
                            let pmm_end = num_params + num_motives + num_minors;
                            let pmm = list_take(spine, pmm_end);
                            let field_start = ctor_args_len - ctor_nfields;
                            let field_args = list_drop(ctor_args, field_start);
                            let post_major = list_drop(spine, major_idx + 1);
                            let rhs_inst = expr_inst_levels(rhs, lvls);
                            let r1 = apply_spine(rhs_inst, pmm);
                            let r2 = apply_spine(r1, field_args);
                            let r3 = apply_spine(r2, post_major);
                            (1, r3),
                        },
                    },
                },
              _ =>
                -- Not a Ctor; fall through to struct-eta-iota.
                try_struct_eta_iota(spine, num_params, num_motives, num_minors,
                                    major_idx, rules, lvls, types),
            },
          _ =>
            -- head not a Const; fall through to struct-eta-iota.
            try_struct_eta_iota(spine, num_params, num_motives, num_minors,
                                major_idx, rules, lvls, types),
        },
    },
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:1824-1869 try_reduce_nat_succ_linear_rec.
  -- Detects `Nat.rec _ base step (Lit n)` with step = `λ _ ih => Nat.succ ih`
  -- and reduces directly to `Lit (base + n)`. Returns (1, result) on hit,
  -- (0, _) on miss.
  fn try_nat_linear_rec(spine: List‹KExpr›, num_params: G, num_motives: G,
                        num_minors: G, major_idx: G,
                        types: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(num_minors, 2) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let raw_major = list_lookup(spine, major_idx);
        let major_w = whnf(raw_major, types);
        match try_extract_nat(major_w) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, n_klimbs) =>
            let base_idx = num_params + num_motives;
            let raw_step = list_lookup(spine, base_idx + 1);
            let step_w = whnf(raw_step, types);
            match is_nat_succ_ih_step(step_w) {
              0 => (0, store(KExprNode.BVar(0))),
              1 =>
                let raw_base = list_lookup(spine, base_idx);
                let base_w = whnf(raw_base, types);
                let post = list_drop(spine, major_idx + 1);
                match try_extract_nat(base_w) {
                  -- Symbolic base: collapse `Nat.rec base (succ-step) (Lit n)`
                  -- to the offset primitive `Nat.add base (Lit n)` rather than
                  -- materializing succ^n(base) via n iota steps. This keeps the
                  -- value in the same compact `base + n` form a literal already
                  -- has, so def-eq converges instead of descending n unary
                  -- succ layers (the UTF-8 `x + 0xC0` pathology).
                  (0, _) => mk_nat_offset_stuck(base_w, n_klimbs, post),
                  (1, b_klimbs) =>
                    (1, apply_spine(mk_nat_lit(klimbs_add(b_klimbs, n_klimbs)), post)),
                },
            },
        },
    }
  }

  -- 1 iff `step` whnf-shape is `λ _ (λ _ (Nat.succ #0))`.
  fn is_nat_succ_ih_step(step: KExpr) -> G {
    match load(step) {
      KExprNode.Lam(_, body1) =>
        match load(body1) {
          KExprNode.Lam(_, body2) =>
            match collect_spine(body2) {
              (head, args) =>
                match load(head) {
                  KExprNode.Const(idx, _) =>
                    let head_addr = cref_std_addr(idx);
                    match address_eq(head_addr, nat_succ_addr()) {
                      0 => 0,
                      1 =>
                        match list_length(args) - 1 {
                          0 =>
                            match load(list_lookup(args, 0)) {
                              KExprNode.BVar(i) => eq_zero(i),
                              _ => 0,
                            },
                          _ => 0,
                        },
                    },
                  _ => 0,
                },
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:1244-1301 try_struct_eta_iota.
  -- Fires when major doesn't reduce to ctor BUT inductive is struct-like
  -- (1 ctor, 0 indices, non-recursive). Synthesizes ctor_app via field
  -- projections from the major. Refuses on Prop-typed structures (Rust
  -- whnf.rs:1283 H3 Prop guard via lean4lean toCtorWhenStruct:51).
  fn try_struct_eta_iota(spine: List‹KExpr›,
                         num_params: G, num_motives: G, num_minors: G,
                         major_idx: G, rules: List‹KRecRule›,
                         lvls: List‹KLevel›, types: List‹KExpr›) -> (G, KExpr) {
    let n_rules = list_length(rules);
    match n_rules {
      1 =>
        let rule = list_lookup(rules, 0);
        match rule {
          KRecRule.Mk(ctor_idx, n_fields, rhs) =>
            let ctor_ci = load(get_ci(ctor_idx));
            match ctor_ci {
              KConstantInfo.Ctor(_, _, induct_idx, _, _, _, _) =>
                let ind_ci = load(get_ci(induct_idx));
                match ind_ci {
                  KConstantInfo.Induct(_, _, _, n_indices, ctor_indices, _, _) =>
                    let n_ctors = list_length(ctor_indices);
                    match n_ctors {
                      1 =>
                        match n_indices {
                          0 =>
                            -- is_rec is computed on demand (the recr flag was
                            -- dropped from Ixon); memoized per induct_idx.
                            match computed_is_rec_ind(induct_idx) {
                              0 =>
                                let major = list_lookup(spine, major_idx);
                                let major_ty = k_infer(major, types);
                                let prop_p = is_prop_type(major_ty, types);
                                match prop_p {
                                  1 => (0, store(KExprNode.BVar(0))),
                                  0 =>
                                    let rhs_inst = expr_inst_levels(rhs, lvls);
                                    let pmm_end = (num_params + num_motives) + num_minors;
                                    let pmm = list_take(spine, pmm_end);
                                    let after_pmm = apply_spine(rhs_inst, pmm);
                                    let with_projs = apply_n_projs(after_pmm, induct_idx, major, n_fields, 0);
                                    let post_major = list_drop(spine, major_idx + 1);
                                    let result = apply_spine(with_projs, post_major);
                                    (1, result),
                                },
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                          _ => (0, store(KExprNode.BVar(0))),
                        },
                      _ => (0, store(KExprNode.BVar(0))),
                    },
                },
            },
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- Mirror: Lean kernel Quot.lift / Quot.ind iota.
  --   Quot.lift α r β f sound (Quot.mk α' r' a) = f a
  --   Quot.ind α r motive m (Quot.mk α' r' a) = m a
  --
  -- spine layout:
  --   Lift: [α, r, β, f, sound, q] (6 args)
  --   Ind:  [α, r, motive, m, q]   (5 args)
  --
  -- For both: locate q (last arg), whnf it, expect head Const that's
  -- Quot(_, _, Ctor) (= Quot.mk). Extract `a` (last arg of Quot.mk's
  -- spine), apply to f or m.
  fn try_quot_iota(kind: QuotKind, spine: List‹KExpr›, types: List‹KExpr›) -> (G, KExpr) {
    match kind {
      QuotKind.Lift => try_quot_lift(spine, types),
      QuotKind.Ind => try_quot_ind(spine, types),
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  fn try_quot_lift(spine: List‹KExpr›, types: List‹KExpr›) -> (G, KExpr) {
    let n = list_length(spine);
    let lt6 = u32_less_than(n, 6);
    match lt6 {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let f = list_lookup(spine, 3);
        let q = list_lookup(spine, 5);
        let a_opt = quot_extract_arg(q, types);
        match a_opt {
          (1, a) =>
            let post = list_drop(spine, 6);
            let result = apply_spine(store(KExprNode.App(f, a)), post);
            (1, result),
          (0, _) => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  fn try_quot_ind(spine: List‹KExpr›, types: List‹KExpr›) -> (G, KExpr) {
    let n = list_length(spine);
    let lt5 = u32_less_than(n, 5);
    match lt5 {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let m = list_lookup(spine, 3);
        let q = list_lookup(spine, 4);
        let a_opt = quot_extract_arg(q, types);
        match a_opt {
          (1, a) =>
            let post = list_drop(spine, 5);
            let result = apply_spine(store(KExprNode.App(m, a)), post);
            (1, result),
          (0, _) => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- WHNF q; if q reduces to `App-spine(Const(Quot.mk), [α, r, a])`,
  -- return (1, a). Else (0, _).
  fn quot_extract_arg(q: KExpr, types: List‹KExpr›) -> (G, KExpr) {
    let q_whnf = whnf(q, types);
    let pair = collect_spine(q_whnf);
    match pair {
      (head, args) =>
        match load(head) {
          KExprNode.Const(idx, _) =>
            let ci = load(get_ci(idx));
            match ci {
              KConstantInfo.Quot(_, _, kind) =>
                match kind {
                  QuotKind.Ctor =>
                    -- Mirror: src/ix/kernel/whnf.rs:2410 Quot.mk has exactly 3 args.
                    -- Strict equality required: extra spine args are ill-typed
                    -- and must not silently reduce.
                    let nargs = list_length(args);
                    match nargs - 3 {
                      0 =>
                        let a = list_lookup(args, 2);
                        (1, a),
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

  fn apply_n_projs(head: KExpr, induct_idx: CRef, major: KExpr, n_fields: G, i: G) -> KExpr {
    match n_fields - i {
      0 => head,
      _ =>
        let proj_node = store(KExprNode.Proj(induct_idx, i, major));
        apply_n_projs(store(KExprNode.App(head, proj_node)), induct_idx, major, n_fields, i + 1),
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:1315-1380 synth_ctor_when_k.
  -- For K-eliminable recursors (1 ctor in Prop, no fields), synthesize
  -- a nullary ctor application from the spine's params so iota fires.
  -- Returns (1, ctor_app) on success, (0, _) on miss. Extracts ctor
  -- universes + params from the major's inferred type (rather than slicing
  -- recursor's lvls or spine), then verifies the synthesized ctor's type
  -- is def-eq with major's type.
  fn try_synth_k_ctor(raw_major: KExpr, num_params: G,
                      rules: List‹KRecRule›, types: List‹KExpr›) -> (G, KExpr) {
    match load(rules) {
      ListNode.Nil => (0, store(KExprNode.BVar(0))),
      ListNode.Cons(rule, _) =>
        match rule {
          KRecRule.Mk(ctor_idx, _, _) =>
            let ctor_ci = load(get_ci(ctor_idx));
            match ctor_ci {
              KConstantInfo.Ctor(_, _, induct_idx, _, _, _, _) =>
                let ind_ci = load(get_ci(induct_idx));
                match ind_ci {
                  KConstantInfo.Induct(_, _, _, _, ctor_indices, _, _) =>
                    let n_ctors = list_length(ctor_indices);
                    match n_ctors {
                      0 => (0, store(KExprNode.BVar(0))),
                      _ =>
                        let first_ctor = list_lookup(ctor_indices, 0);
                        let major_ty = k_infer(raw_major, types);
                        let major_ty_w = whnf(major_ty, types);
                        match collect_spine(major_ty_w) {
                          (ty_head, ty_args) =>
                            match load(ty_head) {
                              KExprNode.Const(ty_ind_idx, ctor_us) =>
                                match cref_eq(ty_ind_idx, induct_idx) {
                                  1 =>
                                    let ctor_head = store(KExprNode.Const(first_ctor, ctor_us));
                                    let params = list_take(ty_args, num_params);
                                    let ctor_app = apply_spine(ctor_head, params);
                                    -- Verify: ctor's inferred type def-eq major's type.
                                    let ctor_ty = k_infer(ctor_app, types);
                                    match k_is_def_eq(major_ty_w, ctor_ty, types) {
                                      1 => (1, ctor_app),
                                      0 => (0, store(KExprNode.BVar(0))),
                                    },
                                  0 => (0, store(KExprNode.BVar(0))),
                                },
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                        },
                    },
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Helpers
  -- ============================================================================
  fn list_lookup_or_nil(list: List‹KExpr›, idx: G) -> KExpr {
    match load(list) {
      ListNode.Nil => store(KExprNode.BVar(0)),
      ListNode.Cons(v, rest) =>
        match idx {
          0 => v,
          _ => list_lookup_or_nil(rest, idx - 1),
        },
    }
  }

  fn ensure_sort_post_whnf(e: KExpr) -> (G, KLevel) {
    match load(e) {
      KExprNode.Srt(l) => (1, l),
      _ => (0, store(KLevelNode.Zero)),
    }
  }

  fn ensure_forall_post_whnf(e: KExpr) -> (G, KExpr, KExpr) {
    match load(e) {
      KExprNode.Forall(ty, body) => (1, ty, body),
      _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
    }
  }
⟧

end IxVM

end
