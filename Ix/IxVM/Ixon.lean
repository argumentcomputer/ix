module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ixon := ⟦
  -- Expression type
  enum Expr {
    Srt(U64),
    Var(U64),
    Ref(U64, List‹U64›),
    Rec(U64, List‹U64›),
    Prj(U64, U64, &Expr),
    Str(U64),
    Nat(U64),
    App(&Expr, &Expr),
    Lam(&Expr, &Expr),
    All(&Expr, &Expr),
    Let(U64, &Expr, &Expr, &Expr),
    Share(U64)
  }

  -- Universe levels
  enum Univ {
    Zero,
    Succ(&Univ),
    Max(&Univ, &Univ),
    IMax(&Univ, &Univ),
    Var(U64)
  }

  -- Definition kind
  enum DefKind {
    Definition,
    Opaque,
    Theorem
  }

  -- Definition safety
  enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial
  }

  -- Quotient kind
  enum QuotKind {
    Typ,
    Ctor,
    Lift,
    Ind
  }

  -- Definition: (kind, safety, lvls, typ, value)
  enum Definition {
    Mk(DefKind, DefinitionSafety, U64, &Expr, &Expr)
  }

  -- RecursorRule: (fields, rhs)
  enum RecursorRule {
    Mk(U64, &Expr)
  }

  -- Recursor: (k, is_unsafe, lvls, params, indices, motives, minors, typ, rules)
  enum Recursor {
    Mk(G, G, U64, U64, U64, U64, U64, &Expr, List‹RecursorRule›)
  }

  -- Axiom: (is_unsafe, lvls, typ)
  enum Axiom {
    Mk(G, U64, &Expr)
  }

  -- Quotient: (kind, lvls, typ)
  enum Quotient {
    Mk(QuotKind, U64, &Expr)
  }

  -- Constructor: (is_unsafe, lvls, cidx, params, fields, typ)
  enum Constructor {
    Mk(G, U64, U64, U64, U64, &Expr)
  }

  -- Inductive: (recr, refl, is_unsafe, lvls, params, indices, nested, typ, ctors)
  enum Inductive {
    Mk(G, G, G, U64, U64, U64, U64, &Expr, List‹Constructor›)
  }

  -- InductiveProj: (idx, block_address)
  enum InductiveProj {
    Mk(U64, Addr)
  }

  -- ConstructorProj: (idx, cidx, block_address)
  enum ConstructorProj {
    Mk(U64, U64, Addr)
  }

  -- RecursorProj: (idx, block_address)
  enum RecursorProj {
    Mk(U64, Addr)
  }

  -- DefinitionProj: (idx, block_address)
  enum DefinitionProj {
    Mk(U64, Addr)
  }

  -- MutConst: constants within a mutual block
  enum MutConst {
    Defn(Definition),
    Indc(Inductive),
    Recr(Recursor)
  }

  -- ConstantInfo: the variant/payload of a constant
  enum ConstantInfo {
    Defn(Definition),
    Recr(Recursor),
    Axio(Axiom),
    Quot(Quotient),
    CPrj(ConstructorProj),
    RPrj(RecursorProj),
    IPrj(InductiveProj),
    DPrj(DefinitionProj),
    Muts(List‹MutConst›)
  }

  -- Constant: (info, sharing, refs, univs)
  enum Constant {
    Mk(ConstantInfo, List‹&Expr›, List‹Addr›, List‹&Univ›)
  }

  -- Blob: decoded literal value associated with a content address
  enum BlobEntry {
    Mk(Addr, U64)
  }

⟧

end IxVM

end
