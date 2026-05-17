module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel2.Infer
public import Ix.IxVM.Kernel2.Inductive

public section

namespace IxVM

/-! ## Kernel2: per-constant type checking scaffold

`check_const` body copied verbatim from `Kernel/Check.lean`. All helpers
it directly calls are stubbed to no-op in this module (Check.lean) or in
sibling modules (Infer.lean, Inductive.lean). Stubs return type-correct
defaults so that the dispatch tree compiles; the asserts inside
`check_const` may still fire on real inputs and need real helpers to
pass.
-/

def check := ⟦
  -- Find the position of `target` in `addrs`. Panics (no Nil arm) if
  -- not present.
  fn find_addr_idx(target: Addr, addrs: List‹Addr›, i: G) -> G {
    match load(addrs) {
      ListNode.Cons(a, rest) =>
        match address_eq(target, a) {
          1 => i,
          0 => find_addr_idx(target, rest, i + 1),
        },
    }
  }

  -- Stub.
  fn validate_const_well_scoped(ci: KConstantInfo, top: List‹&KConstantInfo›) {
    ()
  }

  -- Stub.
  fn is_unsafe_ci(ci: KConstantInfo) -> G {
    0
  }

  -- Stub.
  fn assert_safety(self_unsafe: G, e: KExpr, top: List‹&KConstantInfo›) {
    ()
  }

  -- Stub.
  fn check_quot(self_addr: Addr, kind: QuotKind, num_lvls: G, ty: KExpr,
                top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    ()
  }

  -- ============================================================================
  -- check_const: dispatch per KConstantInfo variant. Copied verbatim
  -- from Kernel/Check.lean.
  -- ============================================================================
  fn check_const(ci: KConstantInfo, pos: G, top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    let _ = validate_const_well_scoped(ci, top);
    let u = is_unsafe_ci(ci);
    match ci {
      KConstantInfo.Axiom(_, ty, _) =>
        let _ = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        let _ = assert_safety(u, ty, top);
        (),

      KConstantInfo.Defn(_, ty, val, _, _) =>
        let _ = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = assert_safety(u, val, top);
        let inferred = k_infer(val, top, addrs);
        let _ = k_ensure_eq(inferred, ty, top, addrs);
        (),

      KConstantInfo.Thm(_, ty, val) =>
        let lvl = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        -- scaffold: stubbed helpers, assert disabled
        -- assert_eq!(level_equal(load(lvl), KLevel.Zero), 1);
        let _ = assert_safety(u, ty, top);
        let _ = assert_safety(u, val, top);
        let inferred = k_infer(val, top, addrs);
        let _ = k_ensure_eq(inferred, ty, top, addrs);
        (),

      KConstantInfo.Opaque(_, ty, val, is_unsafe) =>
        let _ = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = assert_safety(u, val, top);
        match is_unsafe {
          1 => (),
          0 =>
            let inferred = k_infer(val, top, addrs);
            let _ = k_ensure_eq(inferred, ty, top, addrs);
            (),
        },

      KConstantInfo.Quot(num_lvls, ty, kind) =>
        let _ = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        let _ = assert_safety(u, ty, top);
        let self_addr = list_lookup(addrs, pos);
        let _ = check_quot(self_addr, kind, num_lvls, ty, top, addrs);
        (),

      KConstantInfo.Induct(_, ty, n_params, n_indices, ctor_indices,
                          is_rec, _, _, _, block_addr) =>
        let _ = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = check_block_peer_param_agreement(pos, ty, n_params, n_indices,
                                                  block_addr, top, addrs);
        let block_idxs = derive_block_member_idxs(pos, top);
        let _ = validate_block_auxes(block_idxs, top);
        let computed_is_rec = compute_is_rec(ctor_indices, n_params, block_idxs, top);
        -- scaffold: stubbed helpers, assert disabled
        -- assert_eq!(is_rec, computed_is_rec);
        (),

      KConstantInfo.Ctor(_, ty, induct_idx, _, num_params, num_fields, _) =>
        let _ = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = check_ctor_against_inductive_member(pos, ci, top);
        let ind_ci = load(list_lookup(top, induct_idx));
        match ind_ci {
          KConstantInfo.Induct(ind_num_lvls, ind_ty, ind_n_params, ind_n_indices, _, _, _, _, _, _) =>
            -- scaffold: stubbed helpers, assert disabled
            -- assert_eq!(num_params, ind_n_params);
            let _ = check_param_agreement(ind_ty, ty, ind_n_params, top, addrs);
            let _ = check_ctor_return_type(ty, num_params, ind_n_indices, num_fields,
                                           induct_idx, ind_num_lvls);
            let ind_level = get_result_sort_level(ind_ty, ind_n_params + ind_n_indices);
            let _ = check_field_universes(ty, num_params, ind_level,
                                          store(ListNode.Nil), top, addrs);
            let _ = check_positivity(ty, num_params, induct_idx, store(ListNode.Nil), top, addrs);
            (),
        },

      KConstantInfo.Rec(_, ty, _, _, _, _, _, _, _, _) =>
        let _ = k_ensure_sort(ty, store(ListNode.Nil), top, addrs);
        let _ = assert_safety(u, ty, top);
        let _ = check_recursor_member(pos, ci, top, addrs);
        (),
    }
  }

  fn check_canonical_block_sort(top: List‹&KConstantInfo›) {
    ()
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
