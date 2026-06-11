module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Whnf

public section

namespace IxVM

/-! ## Definitional equality over `KExpr`

Mirrors `src/ix/kernel/def_eq.rs`.

Tiered strategy:

1. **Structural alpha-equivalence**: same expression shapes with recursive
   def_eq on sub-expressions. Pointer equality short-circuit.
2. **WHNF**: reduce both sides; retry structural.
3. **Proof irrelevance**: both sides accepted when their inferred type is
   a Prop. Implemented via `is_prop_type_of` over the shared types ctx.
4. **Lazy delta**: simultaneous unfold of both sides when both heads are
   Const(idx) of a Defn/Thm; falls through to Const-Proj / Proj-Const /
   Const-App congruence when applicable.
5. **Lambda eta**: when one side is a `Lam` and the other isn't, wrap the
   non-Lam side as `λ(dom). s #0` (via `expr_lift`) and recurse via the
   structural Lam-Lam arm.
6. **Struct / unit-like eta**: subsingleton Prop ctors and recursive
   single-ctor structures fold via `is_unit_like_type` and the iota
   step in `Whnf.lean::try_struct_eta_iota`.
-/

def defEq := ⟦
  -- ============================================================================
  -- k_is_def_eq
  --
  -- Mirror of `src/ix/kernel/def_eq.rs::is_def_eq`. Returns G:
  -- 1 = def-eq, 0 = not.
  -- ============================================================================
  fn k_is_def_eq(a: KExpr, b: KExpr, types: List‹KExpr›,
                 top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    -- Tier 1: pointer equality short-circuit.
    match ptr_val(a) - ptr_val(b) {
      0 => 1,
      -- Context-trimmed memo key (mirror Rust `def_eq_ctx_key`): decide on the
      -- suffix of `types` reachable from either side; closed pairs (lbr 0) key
      -- to the empty context and share across binder depths.
      _ => k_is_def_eq_core(a, b, ctx_trim(types, lbr_max(expr_lbr(a), expr_lbr(b))), top, addrs),
    }
  }

  fn k_is_def_eq_core(a: KExpr, b: KExpr, types: List‹KExpr›,
                      top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
        -- Tier 1.5: lazy-delta app-congruence pre-WHNF. Mirror:
        -- src/ix/kernel/def_eq.rs:1262-1287 try_def_eq_app. When both
        -- sides share Const(idx, lvls) head with same arg count, recurse
        -- on args directly. Sound: only accepts when args recursively def-eq.
        match try_lazy_delta_app(a, b, types, top, addrs) {
          1 => 1,
          0 =>
        -- Tier 1c: string literal expansion (must run before WHNF). Mirror:
        -- src/ix/kernel/def_eq.rs:295-304. If exactly one side is Lit(Str),
        -- expand to `String.ofList [Char.ofNat c, ...]` ctor form so both
        -- sides reduce in lockstep through delta + iota.
        match try_string_lit_pair(a, b, types, top, addrs) {
          1 => 1,
          0 =>
            -- Tier 2: WHNF both sides.
            let aw = whnf(a, types, top, addrs);
            let bw = whnf(b, types, top, addrs);
            match ptr_val(aw) - ptr_val(bw) {
              0 => 1,
              _ =>
                -- Tier 3: proof irrelevance.
                match try_proof_irrel(aw, bw, types, top, addrs) {
                  1 => 1,
                  0 =>
                    -- Tier 3b: unit-like-type symmetry.
                    match try_unit_like(aw, bw, types, top, addrs) {
                      1 => 1,
                      0 =>
                        -- Tier 3c: struct eta (mirror def_eq.rs:778-784).
                        match try_eta_struct(aw, bw, types, top, addrs) {
                          1 => 1,
                          0 =>
                            match try_eta_struct(bw, aw, types, top, addrs) {
                              1 => 1,
                              0 =>
                                -- Tier 3d: Nat offset (mirror def_eq.rs:751).
                                match try_def_eq_nat(aw, bw, types, top, addrs) {
                                  (1, eq) => eq,
                                  (0, _) =>
                                    -- Tier 4: lazy-delta unfold loop (mirror
                                    -- def_eq.rs:1418-1483 lazy_delta_reduction_step).
                                    -- Both sides may be Const-headed Defn/Thm
                                    -- left stuck by whnf (Opaque hint or Theorem).
                                    -- Unfold one side per rank; recurse.
                                    match lazy_delta_loop(aw, bw, 16, types, top, addrs) {
                                      (1, eq) => eq,
                                      (0, _) => k_is_def_eq_struct(aw, bw, types, top, addrs),
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
        }
  }

  -- Mirror: src/ix/kernel/def_eq.rs:801-818 fn try_proof_irrel.
  fn try_proof_irrel(a: KExpr, b: KExpr, types: List‹KExpr›,
                     top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    let a_ty = k_infer(a, types, top, addrs);
    match is_prop_type(a_ty, types, top, addrs) {
      0 => 0,
      1 =>
        let b_ty = k_infer(b, types, top, addrs);
        k_is_def_eq(a_ty, b_ty, types, top, addrs),
    }
  }

  -- Returns 1 iff `whnf(infer(ty))` is `Sort 0`.
  fn is_prop_type(ty: KExpr, types: List‹KExpr›,
                  top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    let sort = k_infer(ty, types, top, addrs);
    let sort_w = whnf(sort, types, top, addrs);
    match load(sort_w) {
      KExprNode.Srt(l) =>
        match load(l) {
          KLevel.Zero => 1,
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/def_eq.rs:858-905 fn try_unit_like_eq.
  fn try_unit_like(a: KExpr, b: KExpr, types: List‹KExpr›,
                   top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    let ta = k_infer(a, types, top, addrs);
    let ta_w = whnf(ta, types, top, addrs);
    match is_unit_like_type(ta_w, top) {
      0 => 0,
      1 =>
        let tb = k_infer(b, types, top, addrs);
        k_is_def_eq(ta, tb, types, top, addrs),
    }
  }

  -- 1 iff ty is `Const(I, _) args` for non-rec 1-ctor 0-field inductive.
  fn is_unit_like_type(ty: KExpr, top: List‹&KConstantInfo›) -> G {
    match collect_spine(ty) {
      (head, _) =>
        match load(head) {
          KExprNode.Const(idx, _) =>
            let ci = load(list_lookup(top, idx));
            match ci {
              KConstantInfo.Induct(_, _, _, _, ctor_indices, is_rec, _, _, _, _) =>
                match is_rec {
                  1 => 0,
                  0 =>
                    match list_length(ctor_indices) {
                      1 =>
                        let ctor_idx = list_lookup(ctor_indices, 0);
                        let ctor_ci = load(list_lookup(top, ctor_idx));
                        match ctor_ci {
                          KConstantInfo.Ctor(_, _, _, _, _, n_fields, _) =>
                            match n_fields {
                              0 => 1,
                              _ => 0,
                            },
                          _ => 0,
                        },
                      _ => 0,
                    },
                },
              _ => 0,
            },
          _ => 0,
        },
    }
  }

  -- Mirror: src/ix/kernel/def_eq.rs:1007-1018 try_string_lit_expansion,
  -- attempted in both directions.
  fn try_string_lit_pair(a: KExpr, b: KExpr, types: List‹KExpr›,
                         top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    match try_string_lit_one(a, b, types, top, addrs) {
      1 => 1,
      0 => try_string_lit_one(b, a, types, top, addrs),
    }
  }

  fn try_string_lit_one(t: KExpr, s: KExpr, types: List‹KExpr›,
                        top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    match load(t) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Str(bs) =>
            match str_lit_to_ctor(bs, addrs) {
              (1, expanded) => k_is_def_eq(expanded, s, types, top, addrs),
              (0, _) => 0,
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Mirror: src/ix/kernel/def_eq.rs:920-926 fn is_nat_zero.
  fn is_nat_zero(e: KExpr, addrs: List‹Addr›) -> G {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(limbs) => klimbs_is_zero(limbs),
          _ => 0,
        },
      KExprNode.Const(idx, _) =>
        address_eq(list_lookup(addrs, idx), nat_zero_addr()),
      _ => 0,
    }
  }


  -- Decompose a WHNF'd Nat into `base + offset` where `base` is the
  -- non-offset core and `offset` a KLimbs literal. Recognizes:
  --   Lit n               -> (matched, 0-base, n)
  --   Nat.succ e          -> base/offset of e, offset+1
  --   Nat.add e (Lit m)   -> base/offset of e, offset+m
  -- `matched=1` iff `e` is offset-shaped (succ/add/lit). The few succ layers
  -- whnf exposes are peeled, but `Nat.add base (Lit m)` is read in O(1) — so a
  -- `succ^k(x)` chain (which whnf leaves as `succ(Nat.add x (Lit k-1))`)
  -- decomposes to `(x, k)` in O(1) instead of k unary steps.
  fn nat_offset_of(e: KExpr, addrs: List‹Addr›) -> (G, KExpr, KLimbs) {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(n) => (1, mk_nat_lit(store(ListNode.Nil)), n),
          _ => (0, e, store(ListNode.Nil)),
        },
      KExprNode.App(f, a) =>
        match load(f) {
          KExprNode.Const(idx, _) =>
            match address_eq(list_lookup(addrs, idx), nat_succ_addr()) {
              1 =>
                match nat_offset_of(a, addrs) {
                  (_, base, o) => (1, base, klimbs_succ(o)),
                },
              0 => (0, e, store(ListNode.Nil)),
            },
          KExprNode.App(g, x) =>
            match load(g) {
              KExprNode.Const(idx, _) =>
                match address_eq(list_lookup(addrs, idx), nat_add_addr()) {
                  1 =>
                    match load(a) {
                      KExprNode.Lit(alit) =>
                        match alit {
                          KLiteral.Nat(m) =>
                            match nat_offset_of(x, addrs) {
                              (1, base, o) => (1, base, klimbs_add(o, m)),
                              (0, _, _) => (1, x, m),
                            },
                          _ => (0, e, store(ListNode.Nil)),
                        },
                      _ => (0, e, store(ListNode.Nil)),
                    },
                  0 => (0, e, store(ListNode.Nil)),
                },
              _ => (0, e, store(ListNode.Nil)),
            },
          _ => (0, e, store(ListNode.Nil)),
        },
      _ => (0, e, store(ListNode.Nil)),
    }
  }

  -- Mirror: src/ix/kernel/def_eq.rs:953-995 is_def_eq_nat / try_def_eq_offset,
  -- generalized to offset form. Returns (matched, eq). Conservative: only
  -- decides when both sides are offset-shaped with EQUAL offsets (then the
  -- verdict is `base_a ≟ base_b`, sound because `+k` is injective); differing
  -- offsets or non-offset shapes fall back (matched=0) to the generic path.
  -- Collapses `succ^k(x) ≟ succ^k(x)` from k unary steps to one klimbs compare.
  fn try_def_eq_nat(a: KExpr, b: KExpr, types: List‹KExpr›,
                     top: List‹&KConstantInfo›,
                     addrs: List‹Addr›) -> (G, G) {
    let za = is_nat_zero(a, addrs);
    let zb = is_nat_zero(b, addrs);
    match za * zb {
      1 => (1, 1),
      0 =>
        match nat_offset_of(a, addrs) {
          (ma, ba, oa) =>
            match nat_offset_of(b, addrs) {
              (mb, bb, ob) =>
                match ma * mb {
                  0 => (0, 0),
                  _ =>
                    match klimbs_eq(oa, ob) {
                      0 => (0, 0),
                      1 => (1, k_is_def_eq(ba, bb, types, top, addrs)),
                    },
                },
            },
        },
    }
  }

  -- Mirror: src/ix/kernel/def_eq.rs:1105-1231 fn try_eta_struct.
  -- Direction (t, s): s is the candidate ctor-headed side. Asserts s is
  -- App-spine of `Const(ctor)` fully applied, induct is struct-like
  -- (non-rec, 0 indices, 1 ctor), and field-by-field `Proj(induct, i, t)
  -- ≡ s_args[num_params + i]`.
  fn try_eta_struct(t: KExpr, s: KExpr, types: List‹KExpr›,
                    top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    match collect_spine(s) {
      (s_head, s_args) =>
        match load(s_head) {
          KExprNode.Const(cidx, _) =>
            match load(list_lookup(top, cidx)) {
              KConstantInfo.Ctor(_, _, induct_idx, _, num_params, num_fields, _) =>
                let arity_diff = list_length(s_args) - (num_params + num_fields);
                match arity_diff {
                  0 =>
                    match load(list_lookup(top, induct_idx)) {
                      KConstantInfo.Induct(_, _, _, n_indices, ctor_indices, is_rec, _, _, _, _) =>
                        let struct_like = eq_zero(is_rec) * eq_zero(n_indices) *
                                          eq_zero(list_length(ctor_indices) - 1);
                        match struct_like {
                          0 => 0,
                          1 =>
                            compare_struct_fields(induct_idx, num_params,
                                                   num_fields, t, s_args, 0,
                                                   types, top, addrs),
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

  fn compare_struct_fields(induct_idx: G, num_params: G, num_fields: G,
                            t: KExpr, s_args: List‹KExpr›, i: G,
                            types: List‹KExpr›,
                            top: List‹&KConstantInfo›,
                            addrs: List‹Addr›) -> G {
    match num_fields - i {
      0 => 1,
      _ =>
        let proj_expr = store(KExprNode.Proj(induct_idx, i, t));
        let s_field = list_lookup(s_args, num_params + i);
        match k_is_def_eq(proj_expr, s_field, types, top, addrs) {
          0 => 0,
          1 => compare_struct_fields(induct_idx, num_params, num_fields, t,
                                       s_args, i + 1, types, top, addrs),
        },
    }
  }

  -- ============================================================================
  -- Structural comparison + Lambda-eta after WHNF.
  -- ============================================================================
  -- Mirror: src/ix/kernel/def_eq.rs lambda-eta tier (both directions).
  -- Every non-Lam `a` paired with Lam `b` falls through to symmetric eta
  -- expansion (try_eta_expand swap), to accept `λx. axiom x ≡ axiom`.
  fn k_is_def_eq_struct(a: KExpr, b: KExpr, types: List‹KExpr›,
                        top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    match load(a) {
      KExprNode.Srt(la) =>
        match load(b) {
          KExprNode.Srt(lb) => level_equal(load(la), load(lb)),
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },

      KExprNode.BVar(ia) =>
        match load(b) {
          KExprNode.BVar(ib) =>
            match ia - ib {
              0 => 1,
              _ => 0,
            },
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },

      KExprNode.Const(ia, lvls_a) =>
        match load(b) {
          KExprNode.Const(ib, lvls_b) =>
            match ia - ib {
              0 => k_is_def_eq_levels(lvls_a, lvls_b),
              _ => 0,
            },
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },

      KExprNode.App(fa, xa) =>
        match load(b) {
          KExprNode.App(fb, xb) =>
            let f_eq = k_is_def_eq(fa, fb, types, top, addrs);
            match f_eq {
              1 => k_is_def_eq(xa, xb, types, top, addrs),
              0 => 0,
            },
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },

      KExprNode.Lam(ty_a, body_a) =>
        match load(b) {
          KExprNode.Lam(ty_b, body_b) =>
            let ty_eq = k_is_def_eq(ty_a, ty_b, types, top, addrs);
            match ty_eq {
              1 =>
                let inner = store(ListNode.Cons(ty_a, types));
                k_is_def_eq(body_a, body_b, inner, top, addrs),
              0 => 0,
            },
          _ => try_eta_expand(ty_a, body_a, b, types, top, addrs),
        },

      KExprNode.Forall(ty_a, body_a) =>
        match load(b) {
          KExprNode.Forall(ty_b, body_b) =>
            let ty_eq = k_is_def_eq(ty_a, ty_b, types, top, addrs);
            match ty_eq {
              1 =>
                let inner = store(ListNode.Cons(ty_a, types));
                k_is_def_eq(body_a, body_b, inner, top, addrs),
              0 => 0,
            },
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },

      KExprNode.Let(ty_a, val_a, body_a) =>
        match load(b) {
          KExprNode.Let(ty_b, val_b, body_b) =>
            let ty_eq = k_is_def_eq(ty_a, ty_b, types, top, addrs);
            match ty_eq {
              1 =>
                let v_eq = k_is_def_eq(val_a, val_b, types, top, addrs);
                match v_eq {
                  1 =>
                    let inner = store(ListNode.Cons(ty_a, types));
                    k_is_def_eq(body_a, body_b, inner, top, addrs),
                  0 => 0,
                },
              0 => 0,
            },
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },

      KExprNode.Lit(la) =>
        match load(b) {
          KExprNode.Lit(lb) => literal_eq(la, lb),
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },

      KExprNode.Proj(tidx_a, fidx_a, ea) =>
        match load(b) {
          KExprNode.Proj(tidx_b, fidx_b, eb) =>
            let same = eq_zero(tidx_a - tidx_b) * eq_zero(fidx_a - fidx_b);
            match same {
              1 => k_is_def_eq(ea, eb, types, top, addrs),
              0 => 0,
            },
          KExprNode.Lam(ty_b, body_b) => try_eta_expand(ty_b, body_b, a, types, top, addrs),
          _ => 0,
        },
    }
  }

  -- ============================================================================
  -- Lambda eta expansion (Rust def_eq.rs:1068-1100).
  --
  -- We have `λ(ty_a). body_a` on one side and a non-Lam `b` on the other.
  -- Build the wrap `λ(ty_a). (lift(b, 1, 0)) #0` and compare its body
  -- against body_a.
  --
  -- Equivalently: compare `body_a` vs `App(lift(b, 1, 0), BVar(0))`.
  -- ============================================================================
  fn try_eta_expand(ty_a: KExpr, body_a: KExpr, b: KExpr,
                    types: List‹KExpr›,
                    top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    let b_lifted = expr_lift(b, 1, 0);
    let bvar0 = store(KExprNode.BVar(0));
    let b_app = store(KExprNode.App(b_lifted, bvar0));
    let inner = store(ListNode.Cons(ty_a, types));
    k_is_def_eq(body_a, b_app, inner, top, addrs)
  }

  -- ============================================================================
  -- Level list equality.
  -- ============================================================================
  fn k_is_def_eq_levels(a: List‹&KLevel›, b: List‹&KLevel›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(lb, rb) =>
            let l_eq = level_equal(load(la), load(lb));
            match l_eq {
              1 => k_is_def_eq_levels(ra, rb),
              0 => 0,
            },
        },
    }
  }

  -- ============================================================================
  -- Lazy-delta app-congruence (Tier 1.5 of k_is_def_eq).
  -- Mirror: src/ix/kernel/def_eq.rs:1262-1287 try_def_eq_app.
  --
  -- When both sides reduce syntactically to `Const(idx, lvls) ◦ args` with
  -- matching idx, level list, and arg count, recurse on args directly via
  -- k_is_def_eq. Bypasses delta+beta of the def's body for the common
  -- congruence case (`f x ≡ f y` whenever `x ≡ y`).
  --
  -- Sound: returns 1 only when args recursively def-eq; returns 0 to fall
  -- through to the regular WHNF-based pipeline.
  -- ============================================================================
  fn try_lazy_delta_app(a: KExpr, b: KExpr, types: List‹KExpr›,
                        top: List‹&KConstantInfo›, addrs: List‹Addr›) -> G {
    match collect_spine(a) {
      (ah, aa) =>
        match collect_spine(b) {
          (bh, bb) =>
            match load(ah) {
              KExprNode.Const(ai, al) =>
                match load(bh) {
                  KExprNode.Const(bi, bl) =>
                    match ai - bi {
                      0 =>
                        match k_is_def_eq_levels(al, bl) {
                          0 => 0,
                          1 =>
                            let len_a = list_length(aa);
                            let len_b = list_length(bb);
                            match len_a - len_b {
                              0 => is_def_eq_arg_list(aa, bb, types, top, addrs),
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

  fn is_def_eq_arg_list(aa: List‹KExpr›, bb: List‹KExpr›,
                        types: List‹KExpr›, top: List‹&KConstantInfo›,
                        addrs: List‹Addr›) -> G {
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
            match k_is_def_eq(a, b, types, top, addrs) {
              0 => 0,
              1 => is_def_eq_arg_list(ar, br, types, top, addrs),
            },
        },
    }
  }

  -- ============================================================================
  -- Lazy-delta unfold loop (Tier 4 of k_is_def_eq).
  -- Mirror: src/ix/kernel/def_eq.rs:1418-1483 lazy_delta_reduction_step
  -- + outer fuel loop in def_eq.rs:1383-1414.
  --
  -- After Tier 2 whnf may leave both sides stuck on Const-headed
  -- Defn(Opaque) or Thm. Iteratively unfolds one side per rank-cmp:
  --   * Both delta-eligible, ar > br : unfold a.
  --   * Both delta-eligible, ar < br : unfold b.
  --   * Both delta-eligible, ar == br: unfold both.
  --   * Only a eligible: unfold a.
  --   * Only b eligible: unfold b.
  --   * Neither: stuck → fall through to structural compare.
  -- After each unfold, whnf the result and recurse. Fuel-bounded.
  -- ============================================================================
  fn is_delta_eligible(idx: G, top: List‹&KConstantInfo›) -> G {
    let ci = load(list_lookup(top, idx));
    match ci {
      KConstantInfo.Defn(_, _, _, _, _) => 1,
      KConstantInfo.Thm(_, _, _) => 1,
      _ => 0,
    }
  }

  fn delta_rank(idx: G, top: List‹&KConstantInfo›) -> G {
    let ci = load(list_lookup(top, idx));
    match ci {
      KConstantInfo.Defn(_, _, _, _, hint) => hint,
      _ => 0,
    }
  }

  -- Unfold a delta-eligible Const-headed expr to its body[lvls] applied
  -- to the spine. Returns (1, expr2) on success, (0, e) otherwise.
  fn delta_unfold(e: KExpr, top: List‹&KConstantInfo›) -> (G, KExpr) {
    match collect_spine(e) {
      (head, spine) =>
        match load(head) {
          KExprNode.Const(idx, lvls) =>
            let ci = load(list_lookup(top, idx));
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

  -- Mirror: src/ix/kernel/def_eq.rs:1539-1549 try_unfold_proj_app.
  -- If e collects to App-spine on Proj(_, _, inner) where inner is itself
  -- delta-eligible Const-headed, unfold inner's body and rewrap the Proj.
  -- Returns (1, e2) on progress, (0, e) otherwise.
  fn try_unfold_proj_app(e: KExpr, top: List‹&KConstantInfo›) -> (G, KExpr) {
    match collect_spine(e) {
      (head, spine) =>
        match load(head) {
          KExprNode.Proj(tidx, fidx, inner) =>
            match delta_unfold(inner, top) {
              (1, inner2) =>
                let new_head = store(KExprNode.Proj(tidx, fidx, inner2));
                (1, apply_spine(new_head, spine)),
              (0, _) => (0, e),
            },
          _ => (0, e),
        },
    }
  }

  fn lazy_delta_loop(a: KExpr, b: KExpr, fuel: G, types: List‹KExpr›,
                     top: List‹&KConstantInfo›, addrs: List‹Addr›) -> (G, G) {
    match fuel {
      0 => (0, 0),
      _ =>
        match ptr_val(a) - ptr_val(b) {
          0 => (1, 1),
          _ =>
            -- Hoist heads once; structural congruence Tier 1 only fires when
            -- both heads are Const (avoids try_lazy_delta_app's redundant
            -- collect_spine when one side is Proj/Lam/etc).
            -- Mirror src/ix/kernel/def_eq.rs:1418-1495: when one side is
            -- Const-delta-eligible and the other isn't (Proj, Sort, Lam,
            -- Forall, Lit, …), unfold the Const side regardless of the
            -- other head's shape. The (Const, Proj) / (Proj, Const) cases
            -- are subsumed by the generalized step helpers, since
            -- try_unfold_proj_app is a no-op on non-Proj heads.
            match collect_spine(a) {
              (ah, aa) =>
                match collect_spine(b) {
                  (bh, bb) =>
                    match load(ah) {
                      KExprNode.Const(ai, al) =>
                        match load(bh) {
                          KExprNode.Const(bi, bl) =>
                            match try_const_app_congruence(ai, al, aa, bi, bl, bb,
                                                            types, top, addrs) {
                              1 => (1, 1),
                              _ => lazy_delta_step_const_const(ai, bi, a, b, fuel,
                                                                types, top, addrs),
                            },
                          _ => lazy_delta_step_a_const(ai, a, b, fuel, types, top, addrs),
                        },
                      _ =>
                        match load(bh) {
                          KExprNode.Const(bi, _) =>
                            lazy_delta_step_b_const(bi, a, b, fuel, types, top, addrs),
                          _ => (0, 0),
                        },
                    },
                },
            },
        },
    }
  }

  -- Const-vs-Const spine congruence: same idx, def-eq levels, same arity,
  -- pairwise def-eq args. Inner of try_lazy_delta_app without the head
  -- loads (caller already did them).
  fn try_const_app_congruence(ai: G, al: List‹&KLevel›, aa: List‹KExpr›,
                              bi: G, bl: List‹&KLevel›, bb: List‹KExpr›,
                              types: List‹KExpr›, top: List‹&KConstantInfo›,
                              addrs: List‹Addr›) -> G {
    match ai - bi {
      0 =>
        match k_is_def_eq_levels(al, bl) {
          0 => 0,
          1 =>
            let len_a = list_length(aa);
            let len_b = list_length(bb);
            match len_a - len_b {
              0 => is_def_eq_arg_list(aa, bb, types, top, addrs),
              _ => 0,
            },
        },
      _ => 0,
    }
  }

  fn lazy_delta_step_const_const(ai: G, bi: G, a: KExpr, b: KExpr, fuel: G,
                                 types: List‹KExpr›, top: List‹&KConstantInfo›,
                                 addrs: List‹Addr›) -> (G, G) {
    let ae = is_delta_eligible(ai, top);
    let be = is_delta_eligible(bi, top);
    match ae {
      0 =>
        match be {
          0 => (0, 0),
          1 => unfold_b_and_loop(a, b, fuel, types, top, addrs),
          _ => (0, 0),
        },
      1 =>
        match be {
          0 => unfold_a_and_loop(a, b, fuel, types, top, addrs),
          1 =>
            let ar = delta_rank(ai, top);
            let br = delta_rank(bi, top);
            match u32_less_than(br, ar) {
              1 => unfold_a_and_loop(a, b, fuel, types, top, addrs),
              0 =>
                match u32_less_than(ar, br) {
                  1 => unfold_b_and_loop(a, b, fuel, types, top, addrs),
                  0 => unfold_both_and_loop(a, b, fuel, types, top, addrs),
                },
            },
          _ => (0, 0),
        },
      _ => (0, 0),
    }
  }

  -- a is Const-headed at idx ai; b is anything else (Proj, Sort, Lam, …).
  -- Mirror Rust def_eq.rs:1438-1445 (a_delta && !b_delta branch).
  -- If a-delta-eligible, try try_unfold_proj_app(b) (no-op for non-Proj b);
  -- else unfold a.
  fn lazy_delta_step_a_const(ai: G, a: KExpr, b: KExpr, fuel: G,
                              types: List‹KExpr›, top: List‹&KConstantInfo›,
                              addrs: List‹Addr›) -> (G, G) {
    match is_delta_eligible(ai, top) {
      0 => (0, 0),
      1 =>
        match try_unfold_proj_app(b, top) {
          (1, b2) =>
            let bw = whnf(b2, types, top, addrs);
            lazy_delta_loop(a, bw, fuel - 1, types, top, addrs),
          (0, _) => unfold_a_and_loop(a, b, fuel, types, top, addrs),
        },
      _ => (0, 0),
    }
  }

  -- b is Const-headed at idx bi; a is anything else. Symmetric to the above.
  -- Mirror Rust def_eq.rs:1446-1453 (!a_delta && b_delta branch).
  fn lazy_delta_step_b_const(bi: G, a: KExpr, b: KExpr, fuel: G,
                              types: List‹KExpr›, top: List‹&KConstantInfo›,
                              addrs: List‹Addr›) -> (G, G) {
    match is_delta_eligible(bi, top) {
      0 => (0, 0),
      1 =>
        match try_unfold_proj_app(a, top) {
          (1, a2) =>
            let aw = whnf(a2, types, top, addrs);
            lazy_delta_loop(aw, b, fuel - 1, types, top, addrs),
          (0, _) => unfold_b_and_loop(a, b, fuel, types, top, addrs),
        },
      _ => (0, 0),
    }
  }

  fn unfold_a_and_loop(a: KExpr, b: KExpr, fuel: G, types: List‹KExpr›,
                       top: List‹&KConstantInfo›, addrs: List‹Addr›) -> (G, G) {
    match delta_unfold(a, top) {
      (1, a2) =>
        let aw = whnf(a2, types, top, addrs);
        lazy_delta_loop(aw, b, fuel - 1, types, top, addrs),
      (0, _) => (0, 0),
    }
  }

  fn unfold_b_and_loop(a: KExpr, b: KExpr, fuel: G, types: List‹KExpr›,
                       top: List‹&KConstantInfo›, addrs: List‹Addr›) -> (G, G) {
    match delta_unfold(b, top) {
      (1, b2) =>
        let bw = whnf(b2, types, top, addrs);
        lazy_delta_loop(a, bw, fuel - 1, types, top, addrs),
      (0, _) => (0, 0),
    }
  }

  fn unfold_both_and_loop(a: KExpr, b: KExpr, fuel: G, types: List‹KExpr›,
                          top: List‹&KConstantInfo›, addrs: List‹Addr›) -> (G, G) {
    match delta_unfold(a, top) {
      (1, a2) =>
        match delta_unfold(b, top) {
          (1, b2) =>
            let aw = whnf(a2, types, top, addrs);
            let bw = whnf(b2, types, top, addrs);
            lazy_delta_loop(aw, bw, fuel - 1, types, top, addrs),
          (0, _) => (0, 0),
        },
      (0, _) => (0, 0),
    }
  }
⟧

end IxVM

end
