module
public import Ix.Aiur.Meta

public section

namespace IxVM

def kernelTypes := ⟦
  -- ============================================================================
  -- KernelTypes — the addr-first kernel term representation
  --
  -- Every constant reference in a KExpr is a content-hash `Addr`, never a
  -- position. Consumers resolve refs through the memoized `get_ci(addr)`,
  -- so no global constant list has to be threaded to interpret a term.
  --
  -- Precondition: the Lean→Ixon compile alpha-collapses the env before
  -- witness build, so every logical constant has exactly ONE canonical
  -- addr and duplicate Muts wrappers are already merged. The kernel does
  -- no dedup of its own — same content gives the same addr, which the
  -- store interns to the same pointer, so sharing is automatic.
  -- ============================================================================

  -- Universe Levels.
  enum KLevelNode {
    Zero,
    Succ(KLevel),
    Max(KLevel, KLevel),
    IMax(KLevel, KLevel),
    Param(G)
  }

  type KLevel = &KLevelNode

  -- Literals. Nat literals are little-endian U64 limb lists; see Klimbs.
  type KLimbs = List‹U64›

  enum KLiteral {
    Nat(KLimbs),
    Str(ByteStream)
  }

  -- ============================================================================
  -- Expressions — addr-first `Const(Addr, List<KLevel>)`.
  --
  -- Proj carries its structure type as an `Addr` too, not an index, so a
  -- projection is interpretable on its own; consumers resolve it via
  -- `get_ci(addr)` like any other reference.
  -- ============================================================================

  enum KExprNode {
    BVar(G),
    Srt(KLevel),
    Const(Addr, List‹KLevel›),
    App(KExpr, KExpr),
    Lam(KExpr, KExpr),
    Forall(KExpr, KExpr),
    Let(KExpr, KExpr, KExpr),
    Lit(KLiteral),
    Proj(Addr, G, KExpr)
  }

  type KExpr = &KExprNode

  -- collect_spine: peel `App(f, a)` layers. Non-tail, memoized per `e`;
  -- shared sub-spines dedup.
  fn collect_spine(e: KExpr) -> (KExpr, List‹KExpr›) {
    match load(e) {
      KExprNode.App(f, a) =>
        let (head, args) = collect_spine(f);
        (head, list_snoc(args, a)),
      _ => (e, List.Nil),
    }
  }

  -- ============================================================================
  -- Recursor Rule
  --
  -- the kernel: `cidx` identifies the constructor within the parent inductive.
  -- Iota matches by `cidx == ctor.cidx`. Rule's ctor address is
  -- (rec.block_addr, rec.ind_idx, cidx) — implicit from the rec's context.
  -- ============================================================================

  enum KRecRule {
    Mk(G, G, KExpr)
  }

  -- ============================================================================
  -- Constant Info — the kernel addr-first
  --
  -- Ctor / Induct / Rec reference their parent Muts wrapper by
  -- `(block_addr, ind_idx)` pair instead of a synthesized projection
  -- addr. This avoids needing to compute blake3(IPrj(idx, block_addr))
  -- at kernel time. Consumers wanting the parent inductive's KCI call
  -- `get_ci_ind_at(block_addr, ind_idx)`.
  --
  -- CIInduct: (num_levels, type, num_params, num_indices, num_ctors,
  --            is_unsafe, block_addr, ind_idx)
  -- CICtor:   (num_levels, type, block_addr, ind_idx, cidx,
  --            num_params, num_fields, is_unsafe)
  -- CIRec:    (num_levels, type, num_params, num_indices,
  --            num_motives, num_minors, rules, k_flag, is_unsafe,
  --            block_addr, rec_idx)
  -- ============================================================================

  enum KConstantInfo {
    Axiom(G, KExpr, G),
    Defn(G, KExpr, KExpr, DefinitionSafety, G),
    Thm(G, KExpr, KExpr),
    Opaque(G, KExpr, KExpr, G),
    Quot(G, KExpr, QuotKind),
    Induct(G, KExpr, G, G, G, G, Addr, G),
    Ctor(G, KExpr, Addr, G, G, G, G, G),
    Rec(G, KExpr, G, G, G, G, List‹KRecRule›, G, G, Addr, G)
  }

⟧

end IxVM

end
