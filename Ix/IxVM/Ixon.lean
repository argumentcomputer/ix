import Ix.Aiur.Meta

namespace IxVM

def ixon := ⟦
  enum U64List {
    Cons([G; 8], &U64List),
    Nil
  }

  enum Expr {
    Srt([G; 8]),
    Var([G; 8]),
    Ref([G; 8], &U64List),
    Rec([G; 8], &U64List),
    Prj([G; 8], [G; 8], &Expr),
    Str([G; 8]),
    Nat([G; 8]),
    App(&Expr, &Expr),
    Lam(&Expr, &Expr),
    All(&Expr, &Expr),
    Let([G; 8], &Expr, &Expr, &Expr),
    Share([G; 8])
  }
⟧

end IxVM
