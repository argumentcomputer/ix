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
    Param([G; 8])
  }

  enum KLevelList {
    Cons(&KLevel, &KLevelList),
    Nil
  }

  -- ============================================================================
  -- Literals
  -- ============================================================================

  enum KLiteral {
    Nat([G; 8]),
    Str([G; 8])
  }

  -- ============================================================================
  -- Expressions (de Bruijn indexed, no binder info or names)
  -- ============================================================================

  enum KExpr {
    BVar([G; 8]),
    Srt(&KLevel),
    Const([G; 8], &KLevelList),
    App(&KExpr, &KExpr),
    Lam(&KExpr, &KExpr),
    Forall(&KExpr, &KExpr),
    Let(&KExpr, &KExpr, &KExpr),
    Lit(KLiteral),
    Proj([G; 8], [G; 8], &KExpr)
  }

  -- ============================================================================
  -- Values (NbE semantic domain)
  --
  -- VSort:  universe sort
  -- VLit:   literal value
  -- VLam:   closure (domain val, body expr, captured env)
  -- VPi:    dependent function type closure
  -- VCtor:  constructor (const idx, levels, num_params, spine)
  -- VFVar:  free variable with spine (de Bruijn level)
  -- VConst: unreducible constant with spine
  -- VProj:  stuck projection (type idx, field idx, struct val, spine)
  -- ============================================================================

  enum KVal {
    Srt(&KLevel),
    Lit(KLiteral),
    Lam(&KVal, &KExpr, &KValEnv),
    Pi(&KVal, &KExpr, &KValEnv),
    Ctor([G; 8], &KLevelList, [G; 8], &KValList),
    FVar([G; 8], &KValList),
    Const([G; 8], &KLevelList, &KValList),
    Proj([G; 8], [G; 8], &KVal, &KValList),
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
    Regular([G; 8])
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
    Mk([G; 8], [G; 8], &KExpr)
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

  enum KU64List {
    Cons([G; 8], &KU64List),
    Nil
  }

  enum KConstantInfo {
    Axiom([G; 8], &KExpr, G),
    Defn([G; 8], &KExpr, &KExpr, KHints, KSafety),
    Thm([G; 8], &KExpr, &KExpr),
    Opaque([G; 8], &KExpr, &KExpr, G),
    Quot([G; 8], &KExpr, KQuotKind),
    Induct([G; 8], &KExpr, [G; 8], [G; 8], &KU64List, G, G, G),
    Ctor([G; 8], &KExpr, [G; 8], [G; 8], [G; 8], [G; 8], G),
    Rec([G; 8], &KExpr, [G; 8], [G; 8], [G; 8], [G; 8], &KRecRuleList, G, G)
  }

  -- The global environment: a list of constants indexed by position
  enum KConstList {
    Cons(&KConstantInfo, &KConstList),
    Nil
  }
⟧

end IxVM

end
