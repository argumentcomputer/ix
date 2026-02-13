import Ix.Aiur.Meta

namespace IxVM

def ixon := ⟦
  -- Universe list for variable-length universe arguments
  enum UnivList {
    Cons(G, &UnivList),
    Nil
  }

  -- Ixon expression type (alpha-invariant Lean expressions)
  -- Names are stripped, binder info is in metadata
  enum Expr {
    -- Sort/Type at a universe level (index into Constant.univs table)
    Srt(G),
    -- De Bruijn variable
    Var(G),
    -- Reference to top-level constant with universe arguments
    -- First G is index into Constant.refs, UnivList are indices into Constant.univs
    Ref(G, &UnivList),
    -- Mutual recursion reference (index within block) with universe arguments
    -- First G is rec index, UnivList are indices into Constant.univs
    Rec(G, &UnivList),
    -- Projection: (struct_type_ref_idx, field_index, struct_value)
    -- First G is index into Constant.refs table for the struct type
    Prj(G, G, &Expr),
    -- String literal - index into Constant.refs table (address points to blob)
    Str(G),
    -- Natural number literal - index into Constant.refs table (address points to blob)
    Nat(G),
    -- Application: (function, argument)
    App(&Expr, &Expr),
    -- Lambda: (binder_type, body)
    Lam(&Expr, &Expr),
    -- Forall/Pi: (binder_type, body)
    All(&Expr, &Expr),
    -- Let: (non_dep, type, value, body)
    -- non_dep is 0 for dep, 1 for non_dep
    Let(G, &Expr, &Expr, &Expr),
    -- Reference to shared subexpression in MutualBlock.sharing[idx]
    Share(G)
  }
⟧

end IxVM
