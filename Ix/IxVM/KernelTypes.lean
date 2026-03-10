module
public import Ix.Aiur.Meta

public section

namespace IxVM

def kernelTypes := ⟦
  -- ============================================================================
  -- Universe Levels
  -- ============================================================================

  enum KLevel {
    LZero,
    LSucc(&KLevel),
    LMax(&KLevel, &KLevel),
    LIMax(&KLevel, &KLevel),
    LParam([G; 8])
  }

  enum KLevelList {
    LLCons(&KLevel, &KLevelList),
    LLNil
  }

  -- ============================================================================
  -- Literals
  -- ============================================================================

  enum KLiteral {
    LitNat([G; 8]),
    LitStr([G; 8])
  }

  -- ============================================================================
  -- Expressions (de Bruijn indexed, no binder info or names)
  -- ============================================================================

  enum KExpr {
    EBVar([G; 8]),
    ESort(&KLevel),
    EConst([G; 8], &KLevelList),
    EApp(&KExpr, &KExpr),
    ELam(&KExpr, &KExpr),
    EForallE(&KExpr, &KExpr),
    ELetE(&KExpr, &KExpr, &KExpr),
    ELit(KLiteral),
    EProj([G; 8], [G; 8], &KExpr)
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
    VSort(&KLevel),
    VLit(KLiteral),
    VLam(&KVal, &KExpr, &KValEnv),
    VPi(&KVal, &KExpr, &KValEnv),
    VCtor([G; 8], &KLevelList, [G; 8], &KValList),
    VFVar([G; 8], &KValList),
    VConst([G; 8], &KLevelList, &KValList),
    VProj([G; 8], [G; 8], &KVal, &KValList)
  }

  -- Value environment (de Bruijn indexed, front = most recent binder)
  enum KValEnv {
    VECons(&KVal, &KValEnv),
    VENil
  }

  -- Value list (for spines, type contexts)
  enum KValList {
    VLCons(&KVal, &KValList),
    VLNil
  }

  -- ============================================================================
  -- Reducibility Hints
  -- ============================================================================

  enum KHints {
    HOpaque,
    HAbbrev,
    HRegular([G; 8])
  }

  -- ============================================================================
  -- Definition Safety
  -- ============================================================================

  enum KSafety {
    SUnsafe,
    SSafe,
    SPartial
  }

  -- ============================================================================
  -- Quotient Kind
  -- ============================================================================

  enum KQuotKind {
    QType,
    QCtor,
    QLift,
    QInd
  }

  -- ============================================================================
  -- Recursor Rule: (ctor_const_idx, num_fields, rhs)
  -- ============================================================================

  enum KRecRule {
    RRMk([G; 8], [G; 8], &KExpr)
  }

  enum KRecRuleList {
    RRCons(&KRecRule, &KRecRuleList),
    RRNil
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
    KUCons([G; 8], &KU64List),
    KUNil
  }

  enum KConstantInfo {
    CIAxiom([G; 8], &KExpr, G),
    CIDefn([G; 8], &KExpr, &KExpr, KHints, KSafety),
    CIThm([G; 8], &KExpr, &KExpr),
    CIOpaque([G; 8], &KExpr, &KExpr, G),
    CIQuot([G; 8], &KExpr, KQuotKind),
    CIInduct([G; 8], &KExpr, [G; 8], [G; 8], &KU64List, G, G, G),
    CICtor([G; 8], &KExpr, [G; 8], [G; 8], [G; 8], [G; 8], G),
    CIRec([G; 8], &KExpr, [G; 8], [G; 8], [G; 8], [G; 8], &KRecRuleList, G, G)
  }

  -- The global environment: a list of constants indexed by position
  enum KConstList {
    CLCons(&KConstantInfo, &KConstList),
    CLNil
  }
⟧

end IxVM

end
