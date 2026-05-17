module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Kernel2: alternative kernel scaffold

Stubbed `check_all` / `check_const`. `check_const` is a no-op;
`check_all` iterates the const list. `check_canonical_block_sort`
is also a no-op. Real checking logic to be filled in later.
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

  fn check_canonical_block_sort(top: List‹&KConstantInfo›) {
    ()
  }

  fn check_const(ci: KConstantInfo, pos: G, top: List‹&KConstantInfo›, addrs: List‹Addr›) {
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
