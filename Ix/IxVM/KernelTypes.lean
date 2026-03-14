module
public import Ix.Aiur.Meta

public section

namespace IxVM

def kernelTypes := ⟦
  -- ============================================================================
  -- Universe Levels
  -- ============================================================================

  -- TODO: Param index could be G instead of [G; 8] (Goldilocks is big enough)
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

  -- TODO: [G; 8] is insufficient — Nat and String literals are arbitrarily large.
  -- Nat should be a list of u64 limbs (little-endian bignum).
  -- Str should be a list of bytes (or a ByteStream).
  -- This also requires fixing the blob ingress and conversion to produce these types.
  enum KLiteral {
    Nat([G; 8]),
    Str([G; 8])
  }

  -- ============================================================================
  -- Expressions (de Bruijn indexed, no binder info or names)
  -- ============================================================================

  -- TODO: all [G; 8] here (BVar index, Const index, Proj indices) could be G
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
  -- ============================================================================

  -- TODO: all [G; 8] here could be G. In particular, FVar's de Bruijn level
  -- is a runtime counter (not from Ixon) and would benefit most from the change,
  -- since it would simplify depth tracking throughout the kernel to use plain G
  -- arithmetic instead of u64 operations.
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

  -- TODO: Regular hint could be G instead of [G; 8]
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

  -- TODO: ctor_const_idx and num_fields could be G instead of [G; 8]
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

  -- TODO: could be a list of G instead of [G; 8]
  enum KU64List {
    Cons([G; 8], &KU64List),
    Nil
  }

  -- TODO: all [G; 8] fields (num_levels, num_params, num_indices, etc.)
  -- could be G instead. The Goldilocks field is large enough for any
  -- realistic value, and using G would simplify arithmetic throughout
  -- the kernel (native field ops instead of u64_add/u64_sub/u64_eq/etc.).
  -- This requires a corresponding change in Convert.lean to emit G values.
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
