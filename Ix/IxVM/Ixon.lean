module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ixon := ⟦
  -- Expression type
  enum Expr {
    Srt([G; 8]),
    Var([G; 8]),
    Ref([G; 8], List‹U64›),
    Rec([G; 8], List‹U64›),
    Prj([G; 8], [G; 8], &Expr),
    Str([G; 8]),
    Nat([G; 8]),
    App(&Expr, &Expr),
    Lam(&Expr, &Expr),
    All(&Expr, &Expr),
    Let([G; 8], &Expr, &Expr, &Expr),
    Share([G; 8])
  }

  -- Universe levels
  enum Univ {
    Zero,
    Succ(&Univ),
    Max(&Univ, &Univ),
    IMax(&Univ, &Univ),
    Var([G; 8])
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
    Mk(DefKind, DefinitionSafety, [G; 8], &Expr, &Expr)
  }

  -- RecursorRule: (fields, rhs)
  enum RecursorRule {
    Mk([G; 8], &Expr)
  }

  -- Recursor: (k, is_unsafe, lvls, params, indices, motives, minors, typ, rules)
  enum Recursor {
    Mk(G, G, [G; 8], [G; 8], [G; 8], [G; 8], [G; 8], &Expr, List‹RecursorRule›)
  }

  -- Axiom: (is_unsafe, lvls, typ)
  enum Axiom {
    Mk(G, [G; 8], &Expr)
  }

  -- Quotient: (kind, lvls, typ)
  enum Quotient {
    Mk(QuotKind, [G; 8], &Expr)
  }

  -- Constructor: (is_unsafe, lvls, cidx, params, fields, typ)
  enum Constructor {
    Mk(G, [G; 8], [G; 8], [G; 8], [G; 8], &Expr)
  }

  -- Inductive: (recr, refl, is_unsafe, lvls, params, indices, nested, typ, ctors)
  enum Inductive {
    Mk(G, G, G, [G; 8], [G; 8], [G; 8], [G; 8], &Expr, List‹Constructor›)
  }

  -- InductiveProj: (idx, block_address)
  enum InductiveProj {
    Mk([G; 8], [G; 32])
  }

  -- ConstructorProj: (idx, cidx, block_address)
  enum ConstructorProj {
    Mk([G; 8], [G; 8], [G; 32])
  }

  -- RecursorProj: (idx, block_address)
  enum RecursorProj {
    Mk([G; 8], [G; 32])
  }

  -- DefinitionProj: (idx, block_address)
  enum DefinitionProj {
    Mk([G; 8], [G; 32])
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
    Mk(ConstantInfo, List‹&Expr›, List‹[G; 32]›, List‹&Univ›)
  }

  -- Blob: decoded literal value associated with a content address
  enum BlobEntry {
    Mk([G; 32], [G; 8])
  }

⟧

end IxVM

end
