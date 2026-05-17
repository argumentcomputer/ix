module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Kernel2: stub Infer

Trivial no-op versions of `k_ensure_sort` / `k_infer` / `k_ensure_eq`
used by `Kernel2.Check.check_const`. -/

def infer := ⟦
  fn k_ensure_sort(e: KExpr, types: List‹KExpr›,
                   top: List‹&KConstantInfo›, addrs: List‹Addr›) -> &KLevel {
    store(KLevel.Zero)
  }

  fn k_infer(e: KExpr,
             top: List‹&KConstantInfo›, addrs: List‹Addr›) -> KExpr {
    e
  }

  fn k_ensure_eq(actual: KExpr, expected: KExpr,
                 top: List‹&KConstantInfo›, addrs: List‹Addr›) {
    ()
  }
⟧

end IxVM

end
