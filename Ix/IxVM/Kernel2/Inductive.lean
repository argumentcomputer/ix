module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Kernel2: stub Inductive

Trivial no-op versions of inductive checks used by
`Kernel2.Check.check_const`. -/

def inductive_check := ⟦
  fn check_block_peer_param_agreement(self_pos: G, self_ty: KExpr,
                                      self_n_params: G, self_n_indices: G,
                                      block_addr: Addr,
                                      top: List‹&KConstantInfo›,
                                      addrs: List‹Addr›) {
    ()
  }

  fn derive_block_member_idxs(ind_idx: G, top: List‹&KConstantInfo›) -> List‹G› {
    store(ListNode.Nil)
  }

  fn validate_block_auxes(block_idxs: List‹G›, top: List‹&KConstantInfo›) {
    ()
  }

  fn compute_is_rec(ctors: List‹G›, n_params: G, block_idxs: List‹G›,
                    top: List‹&KConstantInfo›) -> G {
    0
  }

  fn check_ctor_against_inductive_member(ctor_idx: G, ci_ctor: KConstantInfo,
                                          top: List‹&KConstantInfo›) {
    ()
  }

  fn check_param_agreement(ta: KExpr, tb: KExpr, n: G,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    ()
  }

  fn check_ctor_return_type(ctor_ty: KExpr,
                            n_params: G, n_indices: G, n_fields: G,
                            ind_idx: G, ind_num_lvls: G) {
    ()
  }

  fn get_result_sort_level(ind_ty: KExpr, n: G) -> KLevel {
    KLevel.Zero
  }

  fn check_field_universes(ctor_ty: KExpr, n_params: G, ind_level: KLevel,
                           types: List‹KExpr›,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    ()
  }

  fn check_positivity(ctor_ty: KExpr, n_params: G, ind_idx: G,
                      types: List‹KExpr›,
                      top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    ()
  }

  fn check_recursor_member(rec_idx: G, ci_rec: KConstantInfo,
                           top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    ()
  }
⟧

end IxVM

end
