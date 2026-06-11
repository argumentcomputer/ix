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
    Proj(G, G, KExpr)
  }

  type KExpr = &KExprNode

  -- Collect an application spine: peel `App(f, a)` layers, returning the head
  -- and the args in application order. The single shared definition for every
  -- kernel caller (whnf, primitive, inductive_check, def_eq) — defined here in
  -- `kernelTypes` so it precedes them all in the merge.
  --
  -- Non-tail (no accumulator): keyed on `e` alone, so Aiur memoization dedups
  -- shared sub-spines across reductions. An accumulator would thread `acc`
  -- through the memo key and block that sharing (tail recursion buys nothing in
  -- Aiur — stack depth is free). `list_snoc` keeps order and is itself memoized.
  fn collect_spine(e: KExpr) -> (KExpr, List‹KExpr›) {
    match load(e) {
      KExprNode.App(f, a) =>
        let (head, args) = collect_spine(f);
        (head, list_snoc(args, a)),
      _ => (e, store(ListNode.Nil)),
    }
  }

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
    Induct(G, KExpr, G, G, List‹G›, G, G, G, G, Addr),
    Ctor(G, KExpr, G, G, G, G, G),
    Rec(G, KExpr, G, G, G, G, List‹KRecRule›, G, G, Addr)
  }

⟧

end IxVM

end
