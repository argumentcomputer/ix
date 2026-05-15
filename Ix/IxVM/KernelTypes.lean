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

  -- ============================================================================
  -- Literals
  -- ============================================================================

  -- Nat bignum: little-endian list of u64 limbs (least-significant first).
  -- E.g. the number 0x1_00000000_00000001 is [1, 1] (two limbs).
  -- Zero is represented as List.Nil.
  type KLimbs = List‹U64›

  enum KLiteral {
    Nat(KLimbs),
    Str(ByteStream)
  }

  -- ============================================================================
  -- Expressions (de Bruijn indexed, no binder info or names)
  -- ============================================================================

  enum KExprNode {
    BVar(G),
    Srt(&KLevel),
    Const(G, List‹&KLevel›),
    App(KExpr, KExpr),
    Lam(KExpr, KExpr),
    Forall(KExpr, KExpr),
    Let(KExpr, KExpr, KExpr),
    Lit(KLiteral),
    Proj(G, G, KExpr),
    -- Free variable carrying its own type. Introduced by `k_infer` when
    -- opening a Lam/Forall/Let body: the bound `BVar(0)` is substituted
    -- with `FVar(fresh, ty)`, decrementing remaining loose BVars. The
    -- index `fresh` is the binder depth at the opening site, so FVars
    -- with the same index refer to the same opened binder. FVar carries
    -- its declared type to avoid threading a separate context for
    -- type-of lookups.
    FVar(G, KExpr)
  }

  type KExpr = &KExprNode

  -- ============================================================================
  -- Values (NbE semantic domain)
  -- ============================================================================

  enum KValNode {
    Srt(&KLevel),
    Lit(KLiteral),
    Lam(KVal, KExpr, KValEnv),
    Pi(KVal, KExpr, KValEnv),
    Ctor(G, List‹&KLevel›, G, List‹KVal›),
    FVar(G, KVal, List‹KVal›),
    Axiom(G, List‹&KLevel›, List‹KVal›),
    Defn(G, List‹&KLevel›, List‹KVal›),
    Thm(G, List‹&KLevel›, List‹KVal›),
    Opaque(G, List‹&KLevel›, List‹KVal›),
    Quot(G, List‹&KLevel›, List‹KVal›),
    Induct(G, List‹&KLevel›, List‹KVal›),
    Rec(G, List‹&KLevel›, List‹KVal›),
    Proj(G, G, KVal, List‹KVal›),
    Thunk(KExpr, KValEnv)
  }

  type KVal = &KValNode

  -- Value environment (de Bruijn indexed, front = most recent binder)
  type KValEnv = List‹KVal›

  -- ============================================================================
  -- Recursor Rule
  --
  -- Mirror: src/ix/kernel/constant.rs::RecRule { ctor, fields, rhs }.
  -- Aiur keeps a global ctor idx in the first slot for direct lookup
  -- convenience. Could be simplified to (fields, rhs) at the cost of an
  -- ingress refactor.
  --
  -- Layout: (global_ctor_idx, num_fields, rhs).
  -- ============================================================================

  enum KRecRule {
    Mk(G, G, KExpr)
  }

  -- ============================================================================
  -- Constant Info
  --
  -- CIAxiom:  (num_levels, type, is_unsafe)
  -- CIDefn:   (num_levels, type, value, safety, hints)
  --
  -- `hints` is a packed G encoding of `Lean.ReducibilityHints`:
  --   0           = Opaque   (never unfold in whnf; lazy-delta-only)
  --   1 + h       = Regular(h)  (h up to 2^32 - 2; height drives lazy-delta priority)
  --   2^32 - 1    = Abbrev   (always unfold, highest priority in lazy-delta)
  -- Larger value = higher delta-rank (unfold first).
  -- Plumbed via secondary IOBuffer key `[2] ++ addr` from Lean side.
  -- CIThm:    (num_levels, type, value)
  -- CIOpaque: (num_levels, type, value, is_unsafe)
  -- CIQuot:   (num_levels, type, kind)
  -- CIInduct: (num_levels, type, num_params, num_indices,
  --            ctor_indices, is_rec, is_reflexive, is_unsafe, nested)
  -- CICtor:   (num_levels, type, induct_idx, cidx,
  --            num_params, num_fields, is_unsafe)
  -- CIRec:    (num_levels, type, num_params, num_indices,
  --            num_motives, num_minors, rules, k_flag, is_unsafe, block_addr)
  -- block_addr = address of the Muts wrapper this Recursor lives in. Used
  -- by canonical_block_sort to validate recursor-block ordering.
  -- ============================================================================

  enum KConstantInfo {
    Axiom(G, KExpr, G),
    Defn(G, KExpr, KExpr, DefinitionSafety, G),
    Thm(G, KExpr, KExpr),
    Opaque(G, KExpr, KExpr, G),
    Quot(G, KExpr, QuotKind),
    Induct(G, KExpr, G, G, List‹G›, G, G, G, G, [G; 32]),
    Ctor(G, KExpr, G, G, G, G, G),
    Rec(G, KExpr, G, G, G, G, List‹KRecRule›, G, G, [G; 32])
  }

⟧

end IxVM

end
