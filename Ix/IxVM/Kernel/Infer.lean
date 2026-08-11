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
  fn k_infer(e: KExpr, types: List‹KExpr›) -> KExpr {
    k_infer_core(e, ctx_trim(types, expr_lbr(e)))
  }

  fn k_infer_core(e: KExpr, types: List‹KExpr›) -> KExpr {
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
            let head_ty = k_infer(head, types);
            k_infer_app_spine_loop(head_ty, args, store(ListNode.Nil), types),
        },

      KExprNode.Lam(ty, body) =>
        k_ensure_sort(ty, types);
        let types2 = store(ListNode.Cons(ty, types));
        let body_ty = k_infer(body, types2);
        store(KExprNode.Forall(ty, body_ty)),

      KExprNode.Forall(ty, body) =>
        let u1 = k_ensure_sort(ty, types);
        let types2 = store(ListNode.Cons(ty, types));
        let u2 = k_ensure_sort(body, types2);
        store(KExprNode.Srt(level_imax(u1, u2))),

      KExprNode.Let(ty, val, body) =>
        k_ensure_sort(ty, types);
        k_check(val, ty, types);
        let body_substed = expr_inst1(body, val, 0);
        k_infer(body_substed, types),

      --  handlers:
      KExprNode.Lit(lit) => k_infer_lit(lit),
      KExprNode.Proj(struct_addr, fidx, e1) =>
        k_infer_proj(struct_addr, fidx, e1, types),
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
  fn k_infer_app_spine_loop(t: KExpr, args: List‹KExpr›,
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
            k_check(a, dom_subst, types);
            k_infer_app_spine_loop(cod, rest,
              store(ListNode.Cons(a, subs_rev)), types),
          _ =>
            let t_concrete = match list_length(subs_rev) {
              0 => t,
              _ => expr_inst_many(t, subs_rev, 0),
            };
            let t_w = whnf(t_concrete, types);
            match load(t_w) {
              KExprNode.Forall(dom, cod) =>
                k_check(a, dom, types);
                k_infer_app_spine_loop(cod, rest,
                  store(ListNode.Cons(a, store(ListNode.Nil))), types),
            },
        },
    }
  }

  -- Canonical primitive addrs (Nat / String). Mirrors
  -- Ix.IxVM.Kernel.Primitive::nat_addr / str_addr — content-hashes
  -- of the primitive constants' Ixon serializations.
  fn nat_addr() -> Addr {
    store([0x39u8, 0x8au8, 0x77u8, 0x06u8, 0xcfu8, 0x13u8, 0xf2u8, 0x23u8,
     0x99u8, 0x2du8, 0x17u8, 0x3du8, 0xceu8, 0x07u8, 0x94u8, 0x68u8,
     0x57u8, 0x24u8, 0x0fu8, 0x49u8, 0xafu8, 0xccu8, 0x74u8, 0x37u8,
     0x23u8, 0xe8u8, 0x39u8, 0xf8u8, 0xf3u8, 0xf2u8, 0xb6u8, 0x31u8])
  }

  fn str_addr() -> Addr {
    store([0x4au8, 0xc0u8, 0x9eu8, 0xd8u8, 0xffu8, 0x61u8, 0xe4u8, 0x4fu8,
     0x11u8, 0x59u8, 0xbcu8, 0x6fu8, 0xb0u8, 0x0fu8, 0xd7u8, 0xe7u8,
     0x2cu8, 0x15u8, 0xdeu8, 0xefu8, 0xeau8, 0x56u8, 0x9du8, 0x75u8,
     0x5du8, 0x8bu8, 0x1du8, 0x05u8, 0xf5u8, 0xd1u8, 0x91u8, 0xf7u8])
  }

  fn k_infer_lit(lit: KLiteral) -> KExpr {
    match lit {
      KLiteral.Nat(_) => store(KExprNode.Const(nat_addr(), store(ListNode.Nil))),
      KLiteral.Str(_) => store(KExprNode.Const(str_addr(), store(ListNode.Nil))),
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
  fn is_inductive_prop(ind_ty: KExpr, lvls: List‹KLevel›, n_skip: G,
                            types: List‹KExpr›) -> G {
    let ind_ty_inst = expr_inst_levels(ind_ty, lvls);
    let result = peel_n_alls_whnf(ind_ty_inst, n_skip, types);
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
  fn peel_n_alls_whnf(e: KExpr, n: G, types: List‹KExpr›) -> KExpr {
    match n {
      0 => whnf(e, types),
      _ =>
        let ew = whnf(e, types);
        match load(ew) {
          KExprNode.Forall(dom, body) =>
            let t2 = store(ListNode.Cons(dom, types));
            peel_n_alls_whnf(body, n - 1, t2),
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
  fn check_prop_field_if_prop(is_prop: G, dom: KExpr,
                                   types: List‹KExpr›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(dom, types);
        assert_eq!(level_equal(lvl, store(KLevelNode.Zero)), 1,
          "projection on a Prop structure: field is not a Prop");
        (),
    }
  }

  -- Mirror crates/kernel/src/infer.rs dependent-data-field guard.
  -- For Prop structures: a preceding data field (sort != 0) whose body
  -- has any loose bvar (`body.lbr() > 0`) makes projection past it unsound.
  -- Matches Rust's `body.lbr() > 0` check exactly.
  fn check_no_dep_data_field_if_prop(is_prop: G, dom: KExpr, body: KExpr,
                                          types: List‹KExpr›) {
    match is_prop {
      0 => (),
      _ =>
        let lvl = k_ensure_sort(dom, types);
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
  fn peel_field_loop(ty: KExpr, target: G, current: G,
                         struct_addr: Addr, val: KExpr, is_prop: G,
                         types: List‹KExpr›) -> KExpr {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match target - current {
          0 =>
            check_prop_field_if_prop(is_prop, dom, types);
            dom,
          _ =>
            check_no_dep_data_field_if_prop(is_prop, dom, body, types);
            let proj_expr = store(KExprNode.Proj(struct_addr, current, val));
            let body_substed = expr_inst1(body, proj_expr, 0);
            peel_field_loop(body_substed, target, current + 1,
                                 struct_addr, val, is_prop, types),
        },
    }
  }

  -- Cold-extracted Proj arm: the widest arm of `k_infer_core` by far
  -- (~10 call sites) on a rare node kind.
  -- Mirror crates/kernel/src/infer.rs infer_proj.
  fn k_infer_proj(struct_addr: Addr, fidx: G, e1: KExpr,
                      types: List‹KExpr›) -> KExpr {
    let val_ty = k_infer(e1, types);
    let wty = whnf(val_ty, types);
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
                    let is_prop = is_inductive_prop(ind_ty, lvls,
                                    n_params + n_indices, types);
                    peel_field_loop(after_params, fidx, 0,
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
  fn k_ensure_sort(e: KExpr, types: List‹KExpr›) -> KLevel {
    let t = k_infer(e, types);
    let tw = whnf(t, types);
    match load(tw) {
      KExprNode.Srt(l) => l,
    }
  }

  -- Check: infer the expr's type, def-eq against expected.
  fn k_check(e: KExpr, expected: KExpr, types: List‹KExpr›) {
    let inferred = k_infer(e, types);
    let d = k_is_def_eq(inferred, expected, types);
    assert_eq!(d, 1, "inferred type is not def-eq to the expected type");
  }

  -- ============================================================================
  -- Decidable dispatch.
  --
  -- Handles `Nat.decLe`/`Nat.decLt`/`Nat.decEq` on literal args. Builds
  -- `Decidable.isTrue prop proof` / `Decidable.isFalse prop proof` with
  -- compiler-emitted witness helpers. `prop` recovered via k_infer on the
  -- (head, arg0, arg1) call expression under the current types context.
  -- ============================================================================

  fn nat_dec_le_addr_dec() -> Addr {
    store([0x08u8, 0xfau8, 0xadu8, 0x5eu8, 0x92u8, 0x31u8, 0x6eu8, 0x17u8,
     0xe5u8, 0xf8u8, 0x08u8, 0x04u8, 0x98u8, 0x2cu8, 0x6fu8, 0x85u8,
     0x3eu8, 0x32u8, 0xbcu8, 0x43u8, 0xf4u8, 0xdcu8, 0x41u8, 0x06u8,
     0x19u8, 0xecu8, 0x13u8, 0xdfu8, 0x15u8, 0x23u8, 0x77u8, 0xe3u8])
  }

  fn nat_dec_eq_addr_dec() -> Addr {
    store([0x67u8, 0x6eu8, 0x87u8, 0xddu8, 0xe5u8, 0xcfu8, 0x30u8, 0xc0u8,
     0x01u8, 0x69u8, 0x0bu8, 0xbbu8, 0xe7u8, 0xabu8, 0x74u8, 0xfcu8,
     0xa9u8, 0x2bu8, 0x0au8, 0xa6u8, 0x12u8, 0xedu8, 0x9eu8, 0xf3u8,
     0xcau8, 0xf8u8, 0x9fu8, 0x1du8, 0x9eu8, 0x6au8, 0x24u8, 0x01u8])
  }

  fn nat_dec_lt_addr_dec() -> Addr {
    store([0xccu8, 0xe1u8, 0x25u8, 0x65u8, 0x0bu8, 0x77u8, 0x5du8, 0x19u8,
     0x10u8, 0xefu8, 0xeau8, 0x91u8, 0x9fu8, 0x5cu8, 0xf2u8, 0x72u8,
     0xf7u8, 0xd9u8, 0xe7u8, 0xb1u8, 0x1du8, 0x62u8, 0x34u8, 0x3du8,
     0x6du8, 0x0au8, 0x58u8, 0x9cu8, 0xdfu8, 0xaeu8, 0xffu8, 0x21u8])
  }

  fn decidable_is_true_addr_dec() -> Addr {
    store([0x0fu8, 0x9eu8, 0xe8u8, 0xd9u8, 0x03u8, 0x3du8, 0x8fu8, 0x7bu8,
     0x85u8, 0x2fu8, 0x5bu8, 0x71u8, 0x52u8, 0xfdu8, 0x12u8, 0x4fu8,
     0x7du8, 0x41u8, 0x19u8, 0x30u8, 0xc9u8, 0x92u8, 0xe0u8, 0xf4u8,
     0x57u8, 0xf8u8, 0x10u8, 0x4bu8, 0x60u8, 0xa9u8, 0x83u8, 0x81u8])
  }

  fn decidable_is_false_addr_dec() -> Addr {
    store([0x04u8, 0x71u8, 0xe4u8, 0x71u8, 0x58u8, 0xb2u8, 0xaeu8, 0x18u8,
     0xd3u8, 0xc0u8, 0x8du8, 0xd5u8, 0xc7u8, 0x7au8, 0xaeu8, 0x23u8,
     0xe6u8, 0x2du8, 0x7bu8, 0xbcu8, 0x1eu8, 0x61u8, 0x11u8, 0x6bu8,
     0xc2u8, 0x81u8, 0x3bu8, 0x13u8, 0x06u8, 0xbcu8, 0x57u8, 0x95u8])
  }

  fn nat_le_of_ble_eq_true_addr_dec() -> Addr {
    store([0xcbu8, 0x1fu8, 0xa5u8, 0xadu8, 0x3eu8, 0x63u8, 0x2cu8, 0x07u8,
     0xb4u8, 0x88u8, 0x28u8, 0xafu8, 0x60u8, 0x4fu8, 0x73u8, 0xc7u8,
     0x0au8, 0x82u8, 0x0bu8, 0x1du8, 0xe4u8, 0xa1u8, 0x3bu8, 0xabu8,
     0xf3u8, 0x1fu8, 0x2bu8, 0x78u8, 0x96u8, 0xf7u8, 0xf9u8, 0xbau8])
  }

  fn nat_not_le_of_not_ble_eq_true_addr_dec() -> Addr {
    store([0xeau8, 0x75u8, 0x61u8, 0xdbu8, 0x25u8, 0xaau8, 0x24u8, 0xceu8,
     0x48u8, 0x1cu8, 0xe3u8, 0xe9u8, 0xeeu8, 0x8du8, 0x70u8, 0x4du8,
     0x48u8, 0x3du8, 0xd9u8, 0x05u8, 0x67u8, 0x57u8, 0xdau8, 0x7eu8,
     0xdau8, 0x24u8, 0xb5u8, 0x11u8, 0x1bu8, 0xe5u8, 0x9bu8, 0xc2u8])
  }

  fn nat_eq_of_beq_eq_true_addr_dec() -> Addr {
    store([0xcbu8, 0x0fu8, 0xf0u8, 0x7du8, 0x3fu8, 0x72u8, 0x26u8, 0xa8u8,
     0x98u8, 0x76u8, 0x9du8, 0xa8u8, 0xcau8, 0xacu8, 0x9au8, 0xc1u8,
     0xb4u8, 0x92u8, 0x26u8, 0xd6u8, 0xaeu8, 0x43u8, 0xb2u8, 0xafu8,
     0xfcu8, 0x84u8, 0x9au8, 0x97u8, 0xf9u8, 0xd3u8, 0xe5u8, 0xc7u8])
  }

  fn nat_ne_of_beq_eq_false_addr_dec() -> Addr {
    store([0x79u8, 0xa5u8, 0x7eu8, 0x7fu8, 0x8du8, 0x10u8, 0x30u8, 0xfbu8,
     0x95u8, 0xffu8, 0x4fu8, 0x19u8, 0xeau8, 0x21u8, 0x2cu8, 0x9au8,
     0xe0u8, 0x11u8, 0x63u8, 0x8fu8, 0xf7u8, 0x34u8, 0x9cu8, 0x4au8,
     0x69u8, 0x2du8, 0xdfu8, 0x5eu8, 0x8eu8, 0x07u8, 0x1au8, 0xd4u8])
  }

  fn bool_type_addr_dec() -> Addr {
    store([0xe6u8, 0xebu8, 0xa3u8, 0xc8u8, 0xb4u8, 0xd1u8, 0x9fu8, 0x6au8,
     0x10u8, 0x76u8, 0xb3u8, 0x9fu8, 0xa8u8, 0x9au8, 0xecu8, 0x61u8,
     0xdcu8, 0xcbu8, 0xb9u8, 0x60u8, 0xf8u8, 0x3du8, 0x9au8, 0x62u8,
     0xe6u8, 0xacu8, 0xf3u8, 0x5au8, 0x69u8, 0xc9u8, 0xa0u8, 0xa4u8])
  }

  fn eq_refl_addr_dec() -> Addr {
    store([0x6cu8, 0x9bu8, 0xd6u8, 0x0eu8, 0x1eu8, 0xaeu8, 0x93u8, 0x8eu8,
     0x56u8, 0x26u8, 0xcau8, 0x23u8, 0x7du8, 0xbcu8, 0xa7u8, 0xfdu8,
     0x95u8, 0x0fu8, 0x2eu8, 0x99u8, 0xe2u8, 0x34u8, 0xa9u8, 0x9cu8,
     0x23u8, 0xcfu8, 0xdcu8, 0x29u8, 0x4cu8, 0xa7u8, 0xadu8, 0xceu8])
  }

  fn int_dec_eq_addr_dec() -> Addr {
    store([0x40u8, 0x2cu8, 0xb0u8, 0x1bu8, 0xfau8, 0x52u8, 0xfeu8, 0x93u8,
     0xaeu8, 0xf3u8, 0xd9u8, 0x6eu8, 0x7du8, 0x28u8, 0xeeu8, 0x03u8,
     0xe0u8, 0xe1u8, 0xf7u8, 0x6fu8, 0x3cu8, 0x87u8, 0x96u8, 0x54u8,
     0xf5u8, 0xe7u8, 0x19u8, 0xa7u8, 0x20u8, 0x15u8, 0x23u8, 0x7fu8])
  }

  fn int_dec_le_addr_dec() -> Addr {
    store([0xbfu8, 0xfeu8, 0xd7u8, 0xcdu8, 0x49u8, 0x68u8, 0xb8u8, 0xfcu8,
     0x25u8, 0x1eu8, 0xd2u8, 0x4au8, 0x9cu8, 0x25u8, 0x3du8, 0xa0u8,
     0x02u8, 0x15u8, 0x90u8, 0x23u8, 0x54u8, 0xc2u8, 0x94u8, 0x4fu8,
     0x59u8, 0xe8u8, 0x15u8, 0x38u8, 0xdcu8, 0x1au8, 0xe2u8, 0xc7u8])
  }

  fn int_dec_lt_addr_dec() -> Addr {
    store([0x09u8, 0xb5u8, 0xfbu8, 0x2fu8, 0x2du8, 0x84u8, 0x51u8, 0x68u8,
     0x9fu8, 0x84u8, 0x27u8, 0x11u8, 0x74u8, 0x4au8, 0x27u8, 0xbfu8,
     0xe5u8, 0x5cu8, 0x6fu8, 0xd5u8, 0x01u8, 0x0fu8, 0xd2u8, 0x4au8,
     0x90u8, 0x84u8, 0x53u8, 0x93u8, 0xc7u8, 0x07u8, 0xe0u8, 0xa4u8])
  }

  fn int_of_nat_addr_dec() -> Addr {
    store([0x09u8, 0xbcu8, 0x25u8, 0x31u8, 0x47u8, 0xc3u8, 0x6cu8, 0xe2u8,
     0x2cu8, 0x8eu8, 0x0cu8, 0xcdu8, 0x43u8, 0xc7u8, 0x9bu8, 0x2cu8,
     0xdau8, 0xe2u8, 0x20u8, 0x6eu8, 0x0du8, 0xddu8, 0x16u8, 0x8fu8,
     0xcau8, 0x36u8, 0x09u8, 0xb2u8, 0xa5u8, 0x84u8, 0xd3u8, 0xdcu8])
  }

  fn int_neg_succ_addr_dec() -> Addr {
    store([0x26u8, 0x7cu8, 0x0au8, 0x9cu8, 0x92u8, 0xe7u8, 0x56u8, 0x38u8,
     0xfcu8, 0x73u8, 0xedu8, 0x52u8, 0xa9u8, 0xf9u8, 0xc8u8, 0x16u8,
     0x47u8, 0xeeu8, 0xecu8, 0xeeu8, 0xffu8, 0x21u8, 0x44u8, 0xc1u8,
     0xf9u8, 0x7eu8, 0x65u8, 0xe2u8, 0xafu8, 0xf1u8, 0x49u8, 0xf1u8])
  }

  fn is_dec_prim_addr(a: Addr) -> G {
    match address_eq(a, nat_dec_le_addr_dec()) {
      1 => 1,
      _ =>
      match address_eq(a, nat_dec_eq_addr_dec()) {
        1 => 1,
        _ =>
        match address_eq(a, nat_dec_lt_addr_dec()) {
          1 => 1,
          _ =>
          match address_eq(a, int_dec_le_addr_dec()) {
            1 => 1,
            _ =>
            match address_eq(a, int_dec_eq_addr_dec()) {
              1 => 1,
              _ =>
              match address_eq(a, int_dec_lt_addr_dec()) {
                1 => 1,
                _ => 0,
              },
            },
          },
        },
      },
    }
  }

  fn is_int_dec_prim_addr(a: Addr) -> G {
    match address_eq(a, int_dec_le_addr_dec()) {
      1 => 1,
      _ =>
      match address_eq(a, int_dec_eq_addr_dec()) {
        1 => 1,
        _ =>
        match address_eq(a, int_dec_lt_addr_dec()) {
          1 => 1,
          _ => 0,
        },
      },
    }
  }

  -- Match `App(Const(int_of_nat|int_neg_succ), Lit(Nat _))`. Returns
  -- (found, sign, limbs). sign=0 for Int.ofNat, 1 for Int.negSucc.
  fn try_extract_int(e: KExpr) -> (G, G, KLimbs) {
    match load(e) {
      KExprNode.App(f, a) =>
        match load(f) {
          KExprNode.Const(caddr, _) =>
            let is_ofnat = address_eq(caddr, int_of_nat_addr_dec());
            let is_negsucc = address_eq(caddr, int_neg_succ_addr_dec());
            match is_ofnat + is_negsucc {
              0 => (0, 0, store(ListNode.Nil)),
              _ =>
                match load(a) {
                  KExprNode.Lit(lit) =>
                    match lit {
                      KLiteral.Nat(limbs) => (1, is_negsucc, limbs),
                      _ => (0, 0, store(ListNode.Nil)),
                    },
                  _ => (0, 0, store(ListNode.Nil)),
                },
            },
          _ => (0, 0, store(ListNode.Nil)),
        },
      _ => (0, 0, store(ListNode.Nil)),
    }
  }

  -- Build canonical `App(Const(int_of_nat | int_neg_succ), Lit(Nat n))`.
  fn intern_int_lit(sign: G, kl: KLimbs) -> KExpr {
    let head_addr = match sign {
      0 => int_of_nat_addr_dec(),
      _ => int_neg_succ_addr_dec(),
    };
    let head = store(KExprNode.Const(head_addr, store(ListNode.Nil)));
    let lit = store(KExprNode.Lit(KLiteral.Nat(kl)));
    store(KExprNode.App(head, lit))
  }

  -- Normalize Int.decLe/decLt/decEq spine args to canonical Int lit
  -- form. If both already canonical, bail (0, _). Otherwise whnf both,
  -- extract, rebuild `App(head, canonical_a, canonical_b, ...post)`.
  -- Caller re-whnfs the rebuilt form; delta then unfolds Int.dec_* body
  -- against canonical inputs.
  fn try_normalize_int_decidable(head_addr: Addr,
                                     head_lvls: List‹KLevel›,
                                     spine: List‹KExpr›,
                                     types: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let a0 = list_lookup(spine, 0);
        let a1 = list_lookup(spine, 1);
        match try_extract_int(a0) {
          (1, _, _) =>
            match try_extract_int(a1) {
              (1, _, _) => (0, store(KExprNode.BVar(0))),
              _ => normalize_int_dec_rebuild(head_addr, head_lvls,
                                              spine, a0, a1, types),
            },
          _ => normalize_int_dec_rebuild(head_addr, head_lvls,
                                          spine, a0, a1, types),
        },
    }
  }

  fn normalize_int_dec_rebuild(head_addr: Addr, head_lvls: List‹KLevel›,
                                spine: List‹KExpr›, a0: KExpr, a1: KExpr,
                                types: List‹KExpr›) -> (G, KExpr) {
    let wa = whnf(a0, types);
    let wb = whnf(a1, types);
    match try_extract_int(wa) {
      (1, sa, na) =>
        match try_extract_int(wb) {
          (1, sb, nb) =>
            let a_e = intern_int_lit(sa, na);
            let b_e = intern_int_lit(sb, nb);
            let head = store(KExprNode.Const(head_addr, head_lvls));
            let r1 = store(KExprNode.App(head, a_e));
            let r2 = store(KExprNode.App(r1, b_e));
            let post = list_drop(spine, 2);
            (1, apply_spine(r2, post)),
          _ => (0, store(KExprNode.BVar(0))),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- Entry point. Whnf calls this on Const-headed apps whose head addr
  -- passes is_dec_prim_addr. Returns (1, reduced) on success or
  -- (0, _) to fall through to Defn unfold.
  fn try_dec_dispatch(head_addr: Addr, head_lvls: List‹KLevel›,
                          spine: List‹KExpr›, types: List‹KExpr›)
                          -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match is_int_dec_prim_addr(head_addr) {
          1 => try_normalize_int_decidable(head_addr, head_lvls,
                                                spine, types),
          _ =>
            let is_le = address_eq(head_addr, nat_dec_le_addr_dec());
            let is_eq = address_eq(head_addr, nat_dec_eq_addr_dec());
            let is_lt = address_eq(head_addr, nat_dec_lt_addr_dec());
            match is_lt {
              1 => dec_rewrite_lt_to_le(head_lvls, spine, types),
              _ => dec_dispatch_le_eq(is_le, is_eq, head_addr,
                                       head_lvls, spine, types),
            },
        },
    }
  }

  -- decLt n m → decLe (n+1) m: rewrite spine head + first arg, return
  -- (1, App(dec_le, succ_n_lit, m_e, ...post)). Whnf caller re-whnfs
  -- the rewritten form, which re-enters dispatch as the decLe arm.
  fn dec_rewrite_lt_to_le(head_lvls: List‹KLevel›, spine: List‹KExpr›,
                           types: List‹KExpr›) -> (G, KExpr) {
    let n_e = list_lookup(spine, 0);
    let m_e = list_lookup(spine, 1);
    let n_w = whnf(n_e, types);
    match try_extract_nat(n_w) {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, n_klimbs) =>
        let succ_lit = mk_nat_lit(klimbs_succ(n_klimbs));
        let dec_le_head = store(KExprNode.Const(
          nat_dec_le_addr_dec(), head_lvls));
        let app1 = store(KExprNode.App(dec_le_head, succ_lit));
        let app2 = store(KExprNode.App(app1, m_e));
        let post = list_drop(spine, 2);
        (1, apply_spine(app2, post)),
    }
  }

  fn dec_dispatch_le_eq(is_le: G, is_eq: G,
                         head_addr: Addr, head_lvls: List‹KLevel›,
                         spine: List‹KExpr›, types: List‹KExpr›)
                         -> (G, KExpr) {
    let n_e = list_lookup(spine, 0);
    let m_e = list_lookup(spine, 1);
    let n_w = whnf(n_e, types);
    let m_w = whnf(m_e, types);
    match try_extract_nat(n_w) {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, n_kl) =>
        match try_extract_nat(m_w) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, m_kl) =>
            let verdict = match is_le {
              1 => klimbs_le(n_kl, m_kl),
              _ => klimbs_eq(n_kl, m_kl),
            };
            dec_build_proof(is_le, is_eq, verdict, n_e, m_e,
                            head_addr, head_lvls, spine, types),
        },
    }
  }

  fn dec_build_proof(is_le: G, is_eq: G, verdict: G,
                      n_e: KExpr, m_e: KExpr,
                      head_addr: Addr, head_lvls: List‹KLevel›,
                      spine: List‹KExpr›, types: List‹KExpr›)
                      -> (G, KExpr) {
    -- Bail decLe-false (needs Bool.noConfusion helper not exposed).
    let bail = is_le * (1 - verdict);
    match bail {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        -- Eq.refl.{1} Bool (Bool.true|Bool.false)
        let one_lvl = store(KLevelNode.Succ(store(KLevelNode.Zero)));
        let eq_refl_lvls = store(ListNode.Cons(one_lvl, store(ListNode.Nil)));
        let eq_refl_c = store(KExprNode.Const(eq_refl_addr_dec(), eq_refl_lvls));
        let bool_c = store(KExprNode.Const(bool_type_addr_dec(), store(ListNode.Nil)));
        let bool_lit_addr = match verdict {
          1 => bool_true_addr(),
          _ => bool_false_addr(),
        };
        let bool_lit_c = store(KExprNode.Const(bool_lit_addr, store(ListNode.Nil)));
        let r1 = store(KExprNode.App(eq_refl_c, bool_c));
        let refl_proof = store(KExprNode.App(r1, bool_lit_c));
        let proof_fn_addr = match is_le {
          1 =>
            match verdict {
              1 => nat_le_of_ble_eq_true_addr_dec(),
              _ => nat_not_le_of_not_ble_eq_true_addr_dec(),
            },
          _ =>
            match verdict {
              1 => nat_eq_of_beq_eq_true_addr_dec(),
              _ => nat_ne_of_beq_eq_false_addr_dec(),
            },
        };
        let proof_c = store(KExprNode.Const(proof_fn_addr, store(ListNode.Nil)));
        let p1 = store(KExprNode.App(proof_c, n_e));
        let p2 = store(KExprNode.App(p1, m_e));
        let proof = store(KExprNode.App(p2, refl_proof));
        dec_finish(verdict, proof, head_addr, head_lvls, spine, types),
    }
  }

  -- String.decEq on two Lit(Str)-whnf'd args → Decidable.isTrue prop
  -- (Eq.refl.{1} String lit) when bytestreams equal. Unequal bails
  -- (no String.noConfusion helper). Entry point invoked from Whnf's
  -- string primitive dispatch when head_addr matches string_dec_eq.
  --
  -- head_addr, spine assumed pre-whnf'd (caller runs whnf_spine).
  fn try_str_dec_eq(head_addr: Addr, spine: List‹KExpr›,
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
                          _ => str_dec_eq_build(sa, head_addr, spine, types),
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

  fn str_dec_eq_build(sa: ByteStream, head_addr: Addr, spine: List‹KExpr›,
                       types: List‹KExpr›) -> (G, KExpr) {
    let one_lvl = store(KLevelNode.Succ(store(KLevelNode.Zero)));
    let eq_refl_lvls = store(ListNode.Cons(one_lvl, store(ListNode.Nil)));
    let eq_refl_c = store(KExprNode.Const(eq_refl_addr_dec(), eq_refl_lvls));
    let str_c = store(KExprNode.Const(string_type_addr(),
                                        store(ListNode.Nil)));
    let lit = store(KExprNode.Lit(KLiteral.Str(sa)));
    let r1 = store(KExprNode.App(eq_refl_c, str_c));
    let refl = store(KExprNode.App(r1, lit));
    -- Recover prop from Decidable prop = infer(head, a0, a1).
    let head_c = store(KExprNode.Const(head_addr, store(ListNode.Nil)));
    let two_args = list_take(spine, 2);
    let call_expr = apply_spine(head_c, two_args);
    let call_ty = k_infer(call_expr, types);
    let call_ty_w = whnf(call_ty, types);
    match collect_spine(call_ty_w) {
      (_, dec_args) =>
        match u32_less_than(list_length(dec_args), 1) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let prop = list_lookup(dec_args, 0);
            let dec_c = store(KExprNode.Const(decidable_is_true_addr_dec(),
                                                store(ListNode.Nil)));
            let d1 = store(KExprNode.App(dec_c, prop));
            let d2 = store(KExprNode.App(d1, refl));
            let post = list_drop(spine, 2);
            (1, apply_spine(d2, post)),
        },
    }
  }

  -- Recover `prop` from `Decidable prop` type of the (head, n, m) call.
  -- Build `Decidable.isTrue prop proof` / `Decidable.isFalse prop proof`.
  fn dec_finish(verdict: G, proof: KExpr, head_addr: Addr,
                 head_lvls: List‹KLevel›, spine: List‹KExpr›,
                 types: List‹KExpr›) -> (G, KExpr) {
    let dec_addr = match verdict {
      1 => decidable_is_true_addr_dec(),
      _ => decidable_is_false_addr_dec(),
    };
    let head_c = store(KExprNode.Const(head_addr, head_lvls));
    let two_args = list_take(spine, 2);
    let call_expr = apply_spine(head_c, two_args);
    let call_ty = k_infer(call_expr, types);
    let call_ty_w = whnf(call_ty, types);
    match collect_spine(call_ty_w) {
      (_, dec_args) =>
        match u32_less_than(list_length(dec_args), 1) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let prop = list_lookup(dec_args, 0);
            let dec_c = store(KExprNode.Const(dec_addr, store(ListNode.Nil)));
            let d1 = store(KExprNode.App(dec_c, prop));
            let d2 = store(KExprNode.App(d1, proof));
            let post = list_drop(spine, 2);
            (1, apply_spine(d2, post)),
        },
    }
  }

⟧

end IxVM

end
