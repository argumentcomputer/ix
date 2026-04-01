module
public import Ix.Aiur.Meta

public section

namespace IxVM

def kernelTypes := ⟦
  -- ============================================================================
  -- Universe Levels
  -- ============================================================================

  enum KLevel {
    Zero,
    Succ(&KLevel),
    Max(&KLevel, &KLevel),
    IMax(&KLevel, &KLevel),
    Param(G)
  }

  enum KLevelList {
    Cons(&KLevel, &KLevelList),
    Nil
  }

  -- ============================================================================
  -- Literals
  -- ============================================================================

  -- Nat bignum: little-endian list of u64 limbs (least-significant first).
  -- E.g. the number 0x1_00000000_00000001 is [1, 1] (two limbs).
  -- Zero is represented as KLimbs.Nil.
  enum KLimbs {
    Nil,
    Cons(U64, &KLimbs)
  }

  enum KLiteral {
    Nat(&KLimbs),
    Str(ByteStream)
  }

  -- ============================================================================
  -- Expressions (de Bruijn indexed, no binder info or names)
  -- ============================================================================

  enum KExpr {
    BVar(G),
    Srt(&KLevel),
    Const(G, &KLevelList),
    App(&KExpr, &KExpr),
    Lam(&KExpr, &KExpr),
    Forall(&KExpr, &KExpr),
    Let(&KExpr, &KExpr, &KExpr),
    Lit(KLiteral),
    Proj(G, G, &KExpr)
  }

  -- ============================================================================
  -- Values (NbE semantic domain)
  -- ============================================================================

  enum KVal {
    Srt(&KLevel),
    Lit(KLiteral),
    Lam(&KVal, &KExpr, &KValEnv),
    Pi(&KVal, &KExpr, &KValEnv),
    Ctor(G, &KLevelList, G, &KValList),
    FVar(G, &KVal, &KValList),
    Const(G, &KLevelList, &KValList),
    Rec(G, &KLevelList, &KValList),
    Proj(G, G, &KVal, &KValList),
    Thunk(&KExpr, &KValEnv)
  }

  -- Value environment (de Bruijn indexed, front = most recent binder)
  enum KValEnv {
    Cons(&KVal, &KValEnv),
    Nil
  }

  -- Value list (for spines, type contexts)
  enum KValList {
    Cons(&KVal, &KValList),
    Nil
  }

  -- ============================================================================
  -- Reducibility Hints
  -- ============================================================================

  enum KHints {
    Opaque,
    Abbrev,
    Regular(G)
  }

  -- ============================================================================
  -- Definition Safety
  -- ============================================================================

  enum KSafety {
    Unsafe,
    Safe,
    Partial
  }

  -- ============================================================================
  -- Quotient Kind
  -- ============================================================================

  enum KQuotKind {
    Typ,
    Ctor,
    Lift,
    Ind
  }

  -- ============================================================================
  -- Recursor Rule: (ctor_const_idx, num_fields, rhs)
  -- ============================================================================

  enum KRecRule {
    Mk(G, G, &KExpr)
  }

  enum KRecRuleMaybe {
    None,
    Some(&KRecRule)
  }

  enum KRecRuleList {
    Cons(&KRecRule, &KRecRuleList),
    Nil
  }

  -- ============================================================================
  -- Constant Info
  --
  -- CIAxiom:  (num_levels, type, is_unsafe)
  -- CIDefn:   (num_levels, type, value, hints, safety)
  -- CIThm:    (num_levels, type, value)
  -- CIOpaque: (num_levels, type, value, is_unsafe)
  -- CIQuot:   (num_levels, type, kind)
  -- CIInduct: (num_levels, type, num_params, num_indices,
  --            ctor_indices, is_rec, is_reflexive, is_unsafe)
  -- CICtor:   (num_levels, type, induct_idx, cidx,
  --            num_params, num_fields, is_unsafe)
  -- CIRec:    (num_levels, type, num_params, num_indices,
  --            num_motives, num_minors, rules, k_flag, is_unsafe)
  -- ============================================================================

  -- List of G values (for kernel constant indices)
  enum KGList {
    Cons(G, &KGList),
    Nil
  }

  -- List of U64 values (for convert inputs from Ixon)
  enum KU64List {
    Cons(U64, &KU64List),
    Nil
  }

  enum KConstantInfo {
    Axiom(G, &KExpr, G),
    Defn(G, &KExpr, &KExpr, KHints, KSafety),
    Thm(G, &KExpr, &KExpr),
    Opaque(G, &KExpr, &KExpr, G),
    Quot(G, &KExpr, KQuotKind),
    Induct(G, &KExpr, G, G, &KGList, G, G, G),
    Ctor(G, &KExpr, G, G, G, G, G),
    Rec(G, &KExpr, G, G, G, G, &KRecRuleList, G, G)
  }

  -- The global environment: a list of constants indexed by position
  enum KConstList {
    Cons(&KConstantInfo, &KConstList),
    Nil
  }
⟧

end IxVM

end
