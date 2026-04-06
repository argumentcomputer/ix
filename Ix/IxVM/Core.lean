module
public import Ix.Aiur.Meta

public section

namespace IxVM

def core := ⟦
  enum List‹T› {
    Cons(T, &List‹T›),
    Nil
  }

  enum Option‹T› {
    Some(T),
    None
  }

  fn list_length‹T›(list: List‹T›) -> G {
    match list {
      List.Nil => 0,
      List.Cons(_, &rest) => list_length(rest) + 1,
    }
  }

  fn list_length_u64‹T›(list: List‹T›) -> U64 {
    match list {
      List.Nil => [0; 8],
      List.Cons(_, &rest) => relaxed_u64_succ(list_length_u64(rest)),
    }
  }

  fn list_concat‹T›(a: List‹T›, b: List‹T›) -> List‹T› {
    match a {
      List.Nil => b,
      List.Cons(v, &rest) => List.Cons(v, store(list_concat(rest, b))),
    }
  }

  fn list_is_empty‹T›(list: List‹T›) -> G {
    match list {
      List.Nil => 1,
      List.Cons(_, _) => 0,
    }
  }

  fn list_lookup‹T›(list: List‹T›, idx: G) -> T {
    let List.Cons(v, &rest) = list;
    match idx {
      0 => v,
      _ => list_lookup(rest, idx - 1),
    }
  }

  fn list_lookup_u64‹T›(list: List‹T›, idx: [G; 8]) -> T {
    let List.Cons(v, &rest) = list;
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
        let List.Cons(_, &rest) = list_drop(list, n - 1);
        rest,
    }
  }

  fn list_take‹T›(list: List‹T›, n: G) -> List‹T› {
    match n {
      0 => List.Nil,
      _ =>
        let List.Cons(v, &rest) = list;
        List.Cons(v, store(list_take(rest, n - 1))),
    }
  }

  fn list_snoc‹T›(list: List‹T›, v: T) -> List‹T› {
    match list {
      List.Nil => List.Cons(v, store(List.Nil)),
      List.Cons(head, &rest) => List.Cons(head, store(list_snoc(rest, v))),
    }
  }
⟧

end IxVM

end
