module
public import Ix.Aiur.Meta

public section

namespace IxVM

def kernelTypes := ⟦
  -- ============================================================================
  -- Universe Levels
  -- ============================================================================

  enum KLevelNode {
    Zero,
    Succ(KLevel),
    Max(KLevel, KLevel),
    IMax(KLevel, KLevel),
    Param(G)
  }

  type KLevel = &KLevelNode

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
  -- Constant references
  --
  -- How kernel expressions name other constants. Replaces the former
  -- global-position scheme (Const(idx) into a flattened closure list):
  -- references resolve lazily by content address via `get_ci`, so the
  -- kernel never enumerates or converts a closure upfront.
  --
  --   Std(addr):        env constant at its content address.
  --   Member(blk, off): flattened member at offset `off` of the Muts block
  --                     at `blk` (peer refs inside mutual blocks; members
  --                     without an env-visible projection constant have no
  --                     own address, so identity is (block, offset)).
  --
  -- Identity compares go through `cref_norm` (Ingress.lean): a Std ref to
  -- a projection constant normalizes to its (block, offset) coordinates,
  -- and block identity uses the content-interned parsed-Constant pointer,
  -- which dedups distinct wrapper addresses with identical parsed content
  -- (mirror of the old `extract_dedup_mptr` canonicalization).
  -- ============================================================================

  enum CRefNode {
    Std(Addr),
    Member(Addr, G)
  }

  type CRef = &CRefNode

  -- ============================================================================
  -- Expressions (de Bruijn indexed, no binder info or names)
  -- ============================================================================

  enum KExprNode {
    BVar(G),
    Srt(KLevel),
    Const(CRef, List‹KLevel›),
    App(KExpr, KExpr),
    Lam(KExpr, KExpr),
    Forall(KExpr, KExpr),
    Let(KExpr, KExpr, KExpr),
    Lit(KLiteral),
    Proj(CRef, G, KExpr)
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
  --
  -- Layout: (ctor_ref, num_fields, rhs). Iota matches a rule by comparing
  -- `ctor_ref` against the major premise's ctor head via `cref_eq`.
  -- ============================================================================

  enum KRecRule {
    Mk(CRef, G, KExpr)
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
  --            ctor_refs, is_unsafe, block_addr)
  -- The recr/refl/nested flags were dropped from Ixon (derivable from
  -- constructor structure; trusting declared values was an adversarial
  -- surface). is_rec is computed on demand via `compute_is_rec`.
  -- CICtor:   (num_levels, type, induct_ref, cidx,
  --            num_params, num_fields, is_unsafe)
  -- CIRec:    (num_levels, type, num_params, num_indices,
  --            num_motives, num_minors, rules, k_flag, is_unsafe, block_addr)
  -- block_addr = raw address of the Muts wrapper this member lives in.
  -- Used by the per-block canonical-order validation and to rebuild
  -- member CRefs.
  -- ============================================================================

  enum KConstantInfo {
    Axiom(G, KExpr, G),
    Defn(G, KExpr, KExpr, DefinitionSafety, G),
    Thm(G, KExpr, KExpr),
    Opaque(G, KExpr, KExpr, G),
    Quot(G, KExpr, QuotKind),
    Induct(G, KExpr, G, G, List‹CRef›, G, Addr),
    Ctor(G, KExpr, CRef, G, G, G, G),
    Rec(G, KExpr, G, G, G, G, List‹KRecRule›, G, G, Addr)
  }

⟧

end IxVM

end
