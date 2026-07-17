/-
  # Merkle: canonical and free-form Merkle trees over `Address` leaves

  Two construction modes share the same hash primitives:

  - **Canonical** (`merkleRootCanonical`): lex-sorted, deduped leaves;
    odd levels padded with a zero sentinel. Used for env merkle roots
    (deterministic env identity) and as the default builder for
    assumption-tree roots.
  - **Free-form** (`merkleJoin`): O(1) composition of two existing
    subtree roots into a new root. Used to aggregate the assumption
    sets of two claims without re-sorting all leaves.

  ## Domain separation

  Leaves are hashed as `blake3(0x00 || addr)` and internal nodes as
  `blake3(0x01 || left || right)`. Follows RFC 6962 (Certificate
  Transparency) convention. Strictly speaking the prefix bytes are
  redundant for our scheme because leaf inputs (32 B) and node inputs
  (64 B) have distinct lengths — so cross-length Blake3 collision is
  the only attack vector and that's infeasible. But the prefix bytes
  make the security argument structural rather than parametric, robust
  under future refactors (variable-length leaves, raw-address mixing)
  and hash swaps (Poseidon2 sponge has fixed arity and doesn't give
  the length argument for free).

  ## Odd-leaf padding

  The canonical builder pads odd levels with a fixed `[0u8; 32]`
  sentinel rather than duplicating the trailing leaf. Duplication
  introduces CVE-2012-2459-style malleability where two distinct leaf
  lists can produce the same root.
-/

module
public import Ix.Address

public section

namespace Ix.Merkle

/-- Domain-separation prefix for leaf hashes. -/
def LEAF_DOMAIN : UInt8 := 0x00

/-- Domain-separation prefix for internal-node hashes. -/
def NODE_DOMAIN : UInt8 := 0x01

/-- 32-byte zero sentinel used as canonical-tree padding. -/
def ZERO_SENTINEL : ByteArray := ⟨Array.replicate 32 0⟩

/-- The fixed zero-sentinel address. -/
def zeroAddress : Address := ⟨ZERO_SENTINEL⟩

/-- Hash a leaf value into its canonical leaf-level digest. -/
def leafHash (addr : Address) : Address :=
  Address.blake3 (⟨#[LEAF_DOMAIN]⟩ ++ addr.hash)

/-- Hash a pair of child digests into their parent internal-node digest. -/
def nodeHash (left right : Address) : Address :=
  Address.blake3 (⟨#[NODE_DOMAIN]⟩ ++ left.hash ++ right.hash)

/--
Combine two existing subtree roots into a new free-form root in O(1).

The result is a non-canonical tree even if both inputs were canonical;
verifiers accept both forms and recover the leaf set by walking the
tree from witness data.
-/
@[inline] def merkleJoin (left right : Address) : Address :=
  nodeHash left right

/-! ## Helpers -/

/-- Sort an Array of Addresses lex-ascending by hash bytes. -/
private def sortAddrs (xs : Array Address) : Array Address :=
  xs.qsort fun a b => compare a b == .lt

/-- Deduplicate a sorted Array of Addresses. -/
private def dedupSortedAddrs (xs : Array Address) : Array Address := Id.run do
  if xs.isEmpty then return #[]
  let mut result : Array Address := #[xs[0]!]
  for i in [1:xs.size] do
    if !(xs[i]! == xs[i-1]!) then
      result := result.push xs[i]!
  return result

/-- One level of the canonical tree: pair adjacent siblings, pad with
zero sentinel if odd count. -/
private def reduceLevel (level : Array Address) : Array Address := Id.run do
  let z := zeroAddress
  let mut next : Array Address := #[]
  let mut i := 0
  while i < level.size do
    let l := level[i]!
    let r := if i + 1 < level.size then level[i+1]! else z
    next := next.push (nodeHash l r)
    i := i + 2
  return next

/-- Reduce a list of nodes to a single root via repeated `reduceLevel`.
Assumes input is non-empty. -/
private partial def buildTree (level : Array Address) : Address :=
  if level.size == 1 then level[0]!
  else buildTree (reduceLevel level)

/-- Build the canonical merkle root over a leaf set. Leaves are
lex-sorted and deduplicated before hashing. Returns:

- `none` if `leaves` is empty (post-dedup).
- `some (leafHash x)` for a single leaf.
- otherwise an internal-node root with odd levels padded by
  `zeroAddress`.
-/
def merkleRootCanonical (leaves : Array Address) : Option Address :=
  let sorted := dedupSortedAddrs (sortAddrs leaves)
  if sorted.isEmpty then
    none
  else if sorted.size == 1 then
    some (leafHash sorted[0]!)
  else
    some (buildTree (sorted.map leafHash))

/-! ## Membership proofs -/

/-- A merkle-path step: `(sibling, isLeft)`. `isLeft = true` means the
sibling sits on the left side at this level, so verification combines
it as `nodeHash sibling current`; otherwise `nodeHash current sibling`. -/
abbrev MerklePath := Array (Address × Bool)

/-- One step of the canonical proof generator: record the sibling at
position `pos` in `level`, then return the next level and updated
position. -/
private def proofStep (level : Array Address) (pos : Nat)
    : (Array Address × Address × Bool × Nat) :=
  let z := zeroAddress
  let siblingIdx := pos ^^^ 1
  let sibling := if h : siblingIdx < level.size then level[siblingIdx] else z
  let isLeft := pos % 2 == 1
  let next := reduceLevel level
  (next, sibling, isLeft, pos / 2)

/-- Produce a sibling-path for `target` in the canonical tree over
`leaves`. Returns `none` if `target` is not in the (post-dedup) leaf
set. Returns the empty path for a single-leaf tree. -/
partial def merkleProofCanonical (leaves : Array Address) (target : Address)
    : Option MerklePath :=
  let sorted := dedupSortedAddrs (sortAddrs leaves)
  if sorted.isEmpty then
    none
  else
    -- Linear find — assumption sets are small in v1.
    let idxOpt := sorted.findIdx? (fun a => a == target)
    match idxOpt with
    | none => none
    | some idx =>
      if sorted.size == 1 then
        some #[]
      else
        some (go (sorted.map leafHash) idx #[])
  where
    go (level : Array Address) (pos : Nat) (acc : MerklePath) : MerklePath :=
      if level.size ≤ 1 then acc
      else
        let (next, sibling, isLeft, pos') := proofStep level pos
        go next pos' (acc.push (sibling, isLeft))

/-- Verify a merkle membership proof against any root (canonical or
free-form). Shape-agnostic — verification just hashes upward. -/
def verifyMerkleProof (root : Address) (leaf : Address)
    (path : MerklePath) : Bool :=
  let final := path.foldl
    (fun current (sibling, isLeft) =>
      if isLeft then nodeHash sibling current else nodeHash current sibling)
    (leafHash leaf)
  final == root

end Ix.Merkle

end
