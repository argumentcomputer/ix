module
public import Ix.Aiur.Meta

public section

namespace IxVM

def templates := ⟦
  enum List‹T› {
    Cons(T, &List‹T›),
    Nil
  }

  enum Option‹T› {
    Some(T),
    None
  }

  fn list_length_u64‹T›(list: List‹T›) -> [G; 8] {
    match list {
      List.Nil => [0; 8],
      List.Cons(_, &rest) => relaxed_u64_succ(list_length_u64(rest)),
    }
  }

  fn list_length_g‹T›(list: List‹T›) -> G {
    match list {
      List.Nil => 0,
      List.Cons(_, &rest) => list_length_g(rest) + 1,
    }
  }
⟧

end IxVM

end
