module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Subst
public import Ix.IxVM.Kernel.Levels
public import Ix.IxVM.Kernel.Whnf
public import Ix.IxVM.Ingress

public section

namespace IxVM

/-! ## Infer-Only

Mirror `with_infer_only` (crates/kernel/src/infer.rs).

Type synthesis ONLY. Skips inner validations: App drops
`k_check(a, dom)`, Lam drops `k_ensure_sort(ty)`, Let drops val/ty
checks, Proj drops prop-field checks.

Called by `try_proof_irrel` inside `k_is_def_eq` — placing it in
its own module breaks the DefEq ↔ Infer cycle.

Safety: MUST NOT be called on ill-typed terms. Callers hand in
subterms already known well-typed (e.g. one whnf'd side of a running
def-eq comparison).
-/

def inferOnly := ⟦
  fn io_types_lookup(types: List‹KExpr›, i: G) -> KExpr {
    let ty = list_lookup(types, i);
    expr_lift(ty, i + 1, 0)
  }

  fn io_const_num_lvls(ci: KConstantInfo) -> G {
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

  fn io_const_type_of(ci: KConstantInfo) -> KExpr {
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

  fn nat_addr_io() -> Addr {
    store([0x39u8, 0x8au8, 0x77u8, 0x06u8, 0xcfu8, 0x13u8, 0xf2u8, 0x23u8,
     0x99u8, 0x2du8, 0x17u8, 0x3du8, 0xceu8, 0x07u8, 0x94u8, 0x68u8,
     0x57u8, 0x24u8, 0x0fu8, 0x49u8, 0xafu8, 0xccu8, 0x74u8, 0x37u8,
     0x23u8, 0xe8u8, 0x39u8, 0xf8u8, 0xf3u8, 0xf2u8, 0xb6u8, 0x31u8])
  }

  fn str_addr_io() -> Addr {
    store([0x4au8, 0xc0u8, 0x9eu8, 0xd8u8, 0xffu8, 0x61u8, 0xe4u8, 0x4fu8,
     0x11u8, 0x59u8, 0xbcu8, 0x6fu8, 0xb0u8, 0x0fu8, 0xd7u8, 0xe7u8,
     0x2cu8, 0x15u8, 0xdeu8, 0xefu8, 0xeau8, 0x56u8, 0x9du8, 0x75u8,
     0x5du8, 0x8bu8, 0x1du8, 0x05u8, 0xf5u8, 0xd1u8, 0x91u8, 0xf7u8])
  }

  -- k_infer_only: type-synthesis-only (mirror Rust `with_infer_only`).
  -- Skips inner validations: App drops `k_check(a, dom)`; Lam drops
  -- `k_ensure_sort(ty)`; Let drops val/ty checks. Distinct Aiur memo from
  -- `k_infer` (parity with Rust's separate infer_cache / infer_only_cache).
  -- Used at try_proof_irrel / is_prop_type / try_unit_like where only the
  -- synthesized type is needed.
  -- ## Safety invariant
  -- `k_infer_only` is NOT safe to call on an arbitrary term — only on terms
  -- already known to be well-typed (i.e., terms that would have passed
  -- `k_infer`). The reason: our overall invariant is that evaluation only
  -- happens after typechecking. `k_infer_only` evaluates types (e.g. the
  -- substitution `B[a/x]` on an `App` arm) WITHOUT first checking that the
  -- substituted-in argument `a` has the proper type (the dropped
  -- `k_check(a, dom)`). On an untyped or ill-typed term, that substitution
  -- can take us out of the well-typed fragment, after which subsequent
  -- `whnf` / `def_eq` work is unsound.
  -- The current call sites (`try_proof_irrel`, `is_prop_type`,
  -- `try_unit_like`) honor this invariant because they hand `k_infer_only`
  -- a term obtained by `whnf`-ing a well-typed input. `whnf` of a
  -- well-typed term yields a structurally different but still well-typed
  -- term, so the no-checks shortcut is sound there even though the result
  -- term itself was never the direct subject of `k_infer`.
  -- ## Future: shared memo via non-deterministic hint
  -- `k_infer_only`'s separate memo (parity with Rust) means an `infer_only`
  -- call cannot reuse an existing `k_infer` hit on the same input. A
  -- planned improvement: at each `try_proof_irrel` / `try_unit_like` site,
  -- the prover supplies a hint `enum Hint { None, KInfer, KInferOnly }`:
  -- 1. `None`         — term is not unit-like and not a proof; skip both
  -- and fall through to deep `def_eq`.
  -- 2. `KInfer`       — `k_infer`'s memo is a hit on this input; call
  -- `k_infer` (cheap, reuses the cached row) and
  -- check the result is a proof / unit-like.
  -- 3. `KInferOnly`   — `k_infer`'s memo would miss; call `k_infer_only`
  -- (cheaper than a fresh `k_infer`) and check.
  -- Dispatching on the hint with a `match` lets us share `k_infer`'s memo
  -- where available and fall back to `k_infer_only` only when the cheaper
  -- path won't pay off, instead of unconditionally paying the parallel
  -- `infer_only` memo cost.
  fn k_infer_only(e: KExpr, types: List‹KExpr›) -> KExpr {
    k_infer_only_core(e, ctx_trim(types, expr_lbr(e)))
  }

  fn k_infer_only_core(e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) => io_types_lookup(types, i),

      KExprNode.Srt(l) =>
        store(KExprNode.Srt(level_reduce(store(KLevelNode.Succ(l))))),

      KExprNode.Const(addr, lvls) =>
        let ci = load(get_ci(addr));
        let expected = io_const_num_lvls(ci);
        assert_eq!(list_length(lvls), expected,
          "Const applied to wrong number of universe levels");
        let ty = io_const_type_of(ci);
        expr_inst_levels(ty, lvls),

      KExprNode.App(f, a) =>
        let f_ty = k_infer_only(f, types);
        match load(f_ty) {
          KExprNode.Forall(_, cod) => expr_inst1(cod, a, 0),
          _ =>
            let f_ty_whnf = whnf(f_ty, types);
            match load(f_ty_whnf) {
              KExprNode.Forall(_, cod) => expr_inst1(cod, a, 0),
            },
        },

      KExprNode.Lam(ty, body) =>
        let types2 = store(ListNode.Cons(ty, types));
        let body_ty = k_infer_only(body, types2);
        store(KExprNode.Forall(ty, body_ty)),

      KExprNode.Forall(ty, body) =>
        let u1 = ensure_sort_only(ty, types);
        let types2 = store(ListNode.Cons(ty, types));
        let u2 = ensure_sort_only(body, types2);
        store(KExprNode.Srt(level_imax(u1, u2))),

      KExprNode.Let(_, val, body) =>
        let body_substed = expr_inst1(body, val, 0);
        k_infer_only(body_substed, types),

      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) =>
            store(KExprNode.Const(nat_addr_io(), store(ListNode.Nil))),
          KLiteral.Str(_) =>
            store(KExprNode.Const(str_addr_io(), store(ListNode.Nil))),
        },

      -- Proj arm: minimal, mirrors k_infer_proj without prop checks.
      KExprNode.Proj(struct_addr, fidx, e1) =>
        let val_ty = k_infer_only(e1, types);
        let wty = whnf(val_ty, types);
        match collect_spine(wty) {
          (head, args) =>
            match load(head) {
              KExprNode.Const(head_addr, lvls) =>
                assert_eq!(ptr_val(head_addr), ptr_val(struct_addr),
                  "projection's structure type differs from the value's head");
                let ind_ci = load(get_ci(head_addr));
                match ind_ci {
                  KConstantInfo.Induct(_, _, n_params, _, num_ctors, _,
                                         block_addr, ind_idx) =>
                    -- Structure requirement, as in `k_infer_proj`. Enforced here
                    -- too: this path skips the inner checks, not the ones that
                    -- decide which constructor's fields are being read.
                    assert_eq!(num_ctors, 1,
                      "projection on an inductive with more than one constructor");
                    let ctor_ci = load(get_ci_cprj(block_addr, ind_idx, 0));
                    match ctor_ci {
                      KConstantInfo.Ctor(_, ctor_ty, _, _, _, _, _, _) =>
                        let ctor_ty_inst = expr_inst_levels(ctor_ty, lvls);
                        let after_params = io_peel_params_subst(ctor_ty_inst, args, n_params);
                        io_peel_field_loop(after_params, fidx, 0, struct_addr, e1),
                    },
                },
            },
        },
    }
  }

  fn ensure_sort_only(e: KExpr, types: List‹KExpr›) -> KLevel {
    let ty = k_infer_only(e, types);
    match load(ty) {
      KExprNode.Srt(l) => l,
      _ =>
        let ty_whnf = whnf(ty, types);
        match load(ty_whnf) {
          KExprNode.Srt(l) => l,
        },
    }
  }

  fn io_peel_params_subst(ty: KExpr, args: List‹KExpr›, n_params: G) -> KExpr {
    match n_params {
      0 => ty,
      _ =>
        match load(ty) {
          KExprNode.Forall(_, body) =>
            match load(args) {
              ListNode.Cons(arg, rest) =>
                let body_substed = expr_inst1(body, arg, 0);
                io_peel_params_subst(body_substed, rest, n_params - 1),
            },
        },
    }
  }

  fn io_peel_field_loop(ty: KExpr, target: G, current: G,
                            struct_addr: Addr, val: KExpr) -> KExpr {
    match load(ty) {
      KExprNode.Forall(dom, body) =>
        match target - current {
          0 => dom,
          _ =>
            let proj_expr = store(KExprNode.Proj(struct_addr, current, val));
            let body_substed = expr_inst1(body, proj_expr, 0);
            io_peel_field_loop(body_substed, target, current + 1,
                                    struct_addr, val),
        },
    }
  }
⟧

end IxVM

end
