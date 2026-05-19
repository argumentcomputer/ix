module
public import Ix.Aiur.Meta

public section

namespace IxVM

def core := ⟦
  enum ListNode‹T› {
    Cons(T, List‹T›),
    Nil
  }

  type List‹T› = &ListNode‹T›

  enum Option‹T› {
    Some(T),
    None
  }

  -- Interned 32-element address (blake3 content hash). Aiur `store`
  -- content-dedups structurally-equal arrays to one canonical pointer,
  -- so address equality reduces to pointer subtraction.
  type Addr = &[G; 32]

  fn list_length‹T›(list: List‹T›) -> G {
    match load(list) {
      ListNode.Nil => 0,
      ListNode.Cons(_, rest) => list_length(rest) + 1,
    }
  }

  fn list_length_u64‹T›(list: List‹T›) -> U64 {
    match load(list) {
      ListNode.Nil => [0; 8],
      ListNode.Cons(_, rest) => relaxed_u64_succ(list_length_u64(rest)),
    }
  }

  fn list_concat‹T›(a: List‹T›, b: List‹T›) -> List‹T› {
    match load(a) {
      ListNode.Nil => b,
      ListNode.Cons(v, rest) => store(ListNode.Cons(v, list_concat(rest, b))),
    }
  }

  fn list_is_empty‹T›(list: List‹T›) -> G {
    match load(list) {
      ListNode.Nil => 1,
      ListNode.Cons(_, _) => 0,
    }
  }

  fn list_lookup‹T›(list: List‹T›, idx: G) -> T {
    let ListNode.Cons(v, rest) = load(list);
    match idx {
      0 => v,
      _ => list_lookup(rest, idx - 1),
    }
  }

  fn list_lookup_u64‹T›(list: List‹T›, idx: [G; 8]) -> T {
    let ListNode.Cons(v, rest) = load(list);
    let z = u64_is_zero(idx);
    match z {
      1 => v,
      0 => list_lookup_u64(rest, relaxed_u64_pred(idx)),
    }
  }

  fn list_drop‹T›(list: List‹T›, n: G) -> List‹T› {
    match n {
      0 => list,
      _ =>
        let ListNode.Cons(_, rest) = load(list_drop(list, n - 1));
        rest,
    }
  }

  fn list_take‹T›(list: List‹T›, n: G) -> List‹T› {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        let ListNode.Cons(v, rest) = load(list);
        store(ListNode.Cons(v, list_take(rest, n - 1))),
    }
  }

  fn list_snoc‹T›(list: List‹T›, v: T) -> List‹T› {
    match load(list) {
      ListNode.Nil => store(ListNode.Cons(v, store(ListNode.Nil))),
      ListNode.Cons(head, rest) => store(ListNode.Cons(head, list_snoc(rest, v))),
    }
  }

  -- O(N) reverse via accumulator. Used by hot-path builders that
  -- accumulate via cons (O(1)) then reverse once instead of O(N²) snoc.
  fn list_reverse‹T›(list: List‹T›) -> List‹T› {
    list_reverse_acc(list, store(ListNode.Nil))
  }

  fn list_reverse_acc‹T›(list: List‹T›, acc: List‹T›) -> List‹T› {
    match load(list) {
      ListNode.Nil => acc,
      ListNode.Cons(head, rest) =>
        list_reverse_acc(rest, store(ListNode.Cons(head, acc))),
    }
  }
⟧

end IxVM

end
