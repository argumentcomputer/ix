module
public import Ix.Aiur.Meta

public section

namespace IxVM

def kernelTypes := ⟦
  -- ============================================================================
  -- Universe Levels
  -- ============================================================================

  -- TODO: Param index could be G instead of U64 (Goldilocks is big enough)
  enum KLevel {
    Zero,
    Succ(&KLevel),
    Max(&KLevel, &KLevel),
    IMax(&KLevel, &KLevel),
    Param(U64)
  }

  enum KLevelList {
    Cons(&KLevel, &KLevelList),
    Nil
  }

  -- ============================================================================
  -- Literals
  -- ============================================================================

  -- TODO: U64 is insufficient — Nat and String literals are arbitrarily large.
  -- Nat should be a list of u64 limbs (little-endian bignum).
  -- Str should be a list of bytes (or a ByteStream).
  -- This also requires fixing the blob ingress and conversion to produce these types.
  enum KLiteral {
    Nat(U64),
    Str(U64)
  }

  -- ============================================================================
  -- Expressions (de Bruijn indexed, no binder info or names)
  -- ============================================================================

  -- TODO: all U64 here (BVar index, Const index, Proj indices) could be G
  enum KExpr {
    BVar(U64),
    Srt(&KLevel),
    Const(U64, &KLevelList),
    App(&KExpr, &KExpr),
    Lam(&KExpr, &KExpr),
    Forall(&KExpr, &KExpr),
    Let(&KExpr, &KExpr, &KExpr),
    Lit(KLiteral),
    Proj(U64, U64, &KExpr)
  }

  -- ============================================================================
  -- Values (NbE semantic domain)
  -- ============================================================================

  -- TODO: all U64 here could be G. In particular, FVar's de Bruijn level
  -- is a runtime counter (not from Ixon) and would benefit most from the change,
  -- since it would simplify depth tracking throughout the kernel to use plain G
  -- arithmetic instead of u64 operations.
  enum KVal {
    Srt(&KLevel),
    Lit(KLiteral),
    Lam(&KVal, &KExpr, &KValEnv),
    Pi(&KVal, &KExpr, &KValEnv),
    Ctor(U64, &KLevelList, U64, &KValList),
    FVar(U64, &KValList),
    Const(U64, &KLevelList, &KValList),
    Proj(U64, U64, &KVal, &KValList),
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

  -- TODO: Regular hint could be G instead of U64
  enum KHints {
    Opaque,
    Abbrev,
    Regular(U64)
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

  -- TODO: ctor_const_idx and num_fields could be G instead of U64
  enum KRecRule {
    Mk(U64, U64, &KExpr)
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

  -- TODO: could be a list of G instead of U64
  enum KU64List {
    Cons(U64, &KU64List),
    Nil
  }

  -- TODO: all U64 fields (num_levels, num_params, num_indices, etc.)
  -- could be G instead. The Goldilocks field is large enough for any
  -- realistic value, and using G would simplify arithmetic throughout
  -- the kernel (native field ops instead of u64_add/u64_sub/u64_eq/etc.).
  -- This requires a corresponding change in Convert.lean to emit G values.
  enum KConstantInfo {
    Axiom(U64, &KExpr, G),
    Defn(U64, &KExpr, &KExpr, KHints, KSafety),
    Thm(U64, &KExpr, &KExpr),
    Opaque(U64, &KExpr, &KExpr, G),
    Quot(U64, &KExpr, KQuotKind),
    Induct(U64, &KExpr, U64, U64, &KU64List, G, G, G),
    Ctor(U64, &KExpr, U64, U64, U64, U64, G),
    Rec(U64, &KExpr, U64, U64, U64, U64, &KRecRuleList, G, G)
  }

  -- The global environment: a list of constants indexed by position
  enum KConstList {
    Cons(&KConstantInfo, &KConstList),
    Nil
  }
⟧

end IxVM

end
