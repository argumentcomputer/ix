/-
  # AssumptionTree: serializable merkle tree over `Address` leaves

  Used to recover the leaf set committed to by a conditional claim's
  `assumptions` root. The root alone tells the verifier *which* set
  was assumed; the AssumptionTree carries the actual leaves so the
  verifier can inspect them.

  Two construction modes — both produce the same `node`-shaped trees,
  differ only in how leaves are arranged:

  - `canonical leaves` builds the same shape that `Ix.Merkle.merkleRootCanonical`
    hashes, with `padding` nodes wherever odd-leaf padding occurs.
  - `join l r` is free-form O(1) composition; result root matches
    `Ix.Merkle.merkleJoin`.

  ## Serialization

  Tag4 size 2 under flag 0xE:

  ```text
  [Tag4(0xE, 2) = 0xE2] [body]

  body recursive:
    leaf(addr):  [0x00] [addr:32]
    padding:     [0x01]
    node(l, r):  [0x02] [body l] [body r]
  ```

  `padding` represents the zero-sentinel slot used by the canonical
  builder to even out odd levels; its root is exactly `zeroAddress`,
  matching the bare 32-byte zero that `Ix.Merkle` mixes into odd-level
  hashing. Splitting it from `leaf` keeps `leaves` clean (returns only
  real leaves, not synthetic padding addresses).
-/

module
public import Ix.Address
public import Ix.Merkle
public import Ix.Ixon

public section

namespace Ix

open Ixon
open Ix.Merkle (leafHash nodeHash zeroAddress merkleJoin)

/-- A merkle tree over `Address` leaves with explicit shape. -/
inductive AssumptionTree where
  | leaf (addr : Address)
  | padding
  | node (left right : AssumptionTree)
  deriving BEq, Repr, Inhabited

namespace AssumptionTree

/-- Recursively compute the root hash. -/
partial def root : AssumptionTree → Address
  | .leaf addr => leafHash addr
  | .padding => zeroAddress
  | .node l r => nodeHash l.root r.root

/-- In-order traversal of real leaves (skips `padding`). Iterative
    stack-based walk to avoid stack overflow on deep trees. -/
partial def leaves (t : AssumptionTree) : Array Address := Id.run do
  let mut acc : Array Address := #[]
  let mut stack : Array AssumptionTree := #[t]
  while !stack.isEmpty do
    let top := stack.back!
    stack := stack.pop
    match top with
    | .leaf a => acc := acc.push a
    | .padding => continue
    | .node l r =>
      -- Push right first so left is processed first (in-order via LIFO).
      stack := stack.push r
      stack := stack.push l
  return acc

/-- True iff `target` appears as a `leaf` somewhere in the tree. -/
partial def contains (t : AssumptionTree) (target : Address) : Bool :=
  match t with
  | .leaf a => a == target
  | .padding => false
  | .node l r => l.contains target || r.contains target

/-- Build the canonical sorted+padded merkle tree over a leaf set.
    Returns `none` for an empty (post-dedup) leaf set. Matches the
    shape committed to by `merkleRootCanonical`. -/
partial def canonical (leaves : Array Address) : Option AssumptionTree :=
  let sorted := dedupSorted (leaves.qsort fun a b => compare a b == .lt)
  if sorted.isEmpty then
    none
  else if sorted.size == 1 then
    some (.leaf sorted[0]!)
  else
    some (reduce (sorted.map .leaf))
  where
    dedupSorted (xs : Array Address) : Array Address := Id.run do
      if xs.isEmpty then return #[]
      let mut acc : Array Address := #[xs[0]!]
      for i in [1:xs.size] do
        if !(xs[i]! == xs[i-1]!) then acc := acc.push xs[i]!
      return acc
    reduce (level : Array AssumptionTree) : AssumptionTree :=
      if level.size == 1 then level[0]!
      else reduce (pairLevel level)
    pairLevel (level : Array AssumptionTree) : Array AssumptionTree := Id.run do
      let mut next : Array AssumptionTree := #[]
      let mut i := 0
      while i < level.size do
        let l := level[i]!
        let r := if i + 1 < level.size then level[i+1]! else .padding
        next := next.push (.node l r)
        i := i + 2
      return next

/-- Combine two existing subtrees into a new free-form node in O(1). -/
@[inline] def join (l r : AssumptionTree) : AssumptionTree := .node l r

/-- Recursive helper for `merkleProof`. Returns the leaf-to-root path
    if `target` is present, else `none`. -/
partial def searchPath (t : AssumptionTree) (target : Address)
    : Option (Array (Address × Bool)) :=
  match t with
  | .leaf a => if a == target then some #[] else none
  | .padding => none
  | .node l r =>
    match l.searchPath target with
    | some p => some (p.push (r.root, false))
    | none =>
      match r.searchPath target with
      | some p => some (p.push (l.root, true))
      | none => none

/-- Produce a merkle membership path for `target`. Path is in
    leaf-to-root order (matches `verifyMerkleProof`). -/
def merkleProof (t : AssumptionTree) (target : Address)
    : Option Ix.Merkle.MerklePath := searchPath t target

/-! ## Serialization -/

def FLAG : UInt8 := 0xE
def VARIANT : UInt64 := 2

def BODY_LEAF    : UInt8 := 0x00
def BODY_PADDING : UInt8 := 0x01
def BODY_NODE    : UInt8 := 0x02

partial def putBody : AssumptionTree → PutM Unit
  | .leaf addr => do
    putU8 BODY_LEAF
    Serialize.put addr
  | .padding => do
    putU8 BODY_PADDING
  | .node l r => do
    putU8 BODY_NODE
    putBody l
    putBody r

def put (t : AssumptionTree) : PutM Unit := do
  putTag4 ⟨FLAG, VARIANT⟩
  putBody t

partial def getBody : GetM AssumptionTree := do
  let tag : UInt8 ← getU8
  if tag == BODY_LEAF then
    return .leaf (← Serialize.get)
  else if tag == BODY_PADDING then
    return .padding
  else if tag == BODY_NODE then
    let l ← getBody
    let r ← getBody
    return .node l r
  else
    throw s!"AssumptionTree.getBody: invalid body tag {tag.toNat}"

def get : GetM AssumptionTree := do
  let tag ← getTag4
  if tag.flag != FLAG || tag.size != VARIANT then
    throw s!"AssumptionTree.get: expected Tag4 0xE/2, got {tag.flag.toNat}/{tag.size}"
  getBody

def ser (t : AssumptionTree) : ByteArray := runPut (put t)
def de (bytes : ByteArray) : Except String AssumptionTree :=
  runGet get bytes

end AssumptionTree

end Ix

end
