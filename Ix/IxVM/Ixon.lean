module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ixon := ⟦
  -- Expression type
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

  -- Universe levels
  enum Univ {
    Zero,
    Succ(&Univ),
    Max(&Univ, &Univ),
    IMax(&Univ, &Univ),
    Var([G; 8])
  }

  enum ExprList {
    Cons(&Expr, &ExprList),
    Nil
  }

  enum UnivList {
    Cons(&Univ, &UnivList),
    Nil
  }

  enum AddressList {
    Cons([G; 32], &AddressList),
    Nil
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

  enum RecursorRuleList {
    Cons(RecursorRule, &RecursorRuleList),
    Nil
  }

  -- Recursor: (k, is_unsafe, lvls, params, indices, motives, minors, typ, rules)
  enum Recursor {
    Mk(G, G, [G; 8], [G; 8], [G; 8], [G; 8], [G; 8], &Expr, &RecursorRuleList)
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

  enum ConstructorList {
    Cons(Constructor, &ConstructorList),
    Nil
  }

  -- Inductive: (recr, refl, is_unsafe, lvls, params, indices, nested, typ, ctors)
  enum Inductive {
    Mk(G, G, G, [G; 8], [G; 8], [G; 8], [G; 8], &Expr, &ConstructorList)
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

  enum MutConstList {
    Cons(MutConst, &MutConstList),
    Nil
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
    Muts(&MutConstList)
  }

  -- Constant: (info, sharing, refs, univs)
  enum Constant {
    Mk(ConstantInfo, &ExprList, &AddressList, &UnivList)
  }
⟧

end IxVM

end
