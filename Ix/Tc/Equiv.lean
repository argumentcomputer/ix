module

public import Ix.Address

/-!
Mirror: crates/kernel/src/equiv.rs

Union-find (disjoint set) for context-aware definitional-equality caching:
weighted quick-union with path halving, keyed by expression hash, context
hash, the requested context-suffix radius, and the expression's intrinsic
local-binder radius.

Pure port: operations return the updated manager (path halving mutates on
reads). Do not reuse the `IO.Ref`-based `Ix.UnionFind`.
-/

public section
@[expose] section

namespace Ix.Tc

/-- Composite key for one expression in one context-suffix interpretation.

The radius is semantically load-bearing even when two suffix calculations
emit the same digest: DefEq transport is only justified between executions
that requested the same radius.  Retaining it here prevents union-find
transitivity from silently joining equality proofs made at different
context-suffix radii. -/
structure EqKey where
  exprAddr : Address
  ctxAddr : Address
  /-- Radius at which `ctxAddr` was computed for this comparison. -/
  lbr : UInt64
  /-- Intrinsic local-binder radius of the expression at `exprAddr`. -/
  exprLbr : UInt64
deriving Inhabited

instance : BEq EqKey where
  beq left right :=
    left.exprAddr == right.exprAddr &&
      left.ctxAddr == right.ctxAddr &&
      left.lbr == right.lbr &&
      left.exprLbr == right.exprLbr

instance : Hashable EqKey where
  hash key := hash (key.exprAddr, key.ctxAddr, key.lbr, key.exprLbr)

/-- Whether two union-find representatives can safely reuse a DefEq cache
context.  Besides retaining the requested scope, their intrinsic expression
radii must reconstruct the radius at which that context digest was made. -/
def EqKey.rootCacheScopeMatches (left right : EqKey)
    (ctxAddr : Address) (lbr : UInt64) : Bool :=
  left.ctxAddr == ctxAddr && right.ctxAddr == ctxAddr &&
    left.lbr == lbr && right.lbr == lbr &&
    max left.exprLbr right.exprLbr == lbr

/-- Union-find for tracking definitional equality between context-aware
    expression keys. -/
structure EquivManager where
  /-- Map from composite key to union-find node index. -/
  keyToNode : Std.HashMap EqKey Nat := {}
  /-- `parent[i]` = parent of node `i`; root iff `parent[i] == i`. -/
  parent : Array Nat := #[]
  /-- Upper bound on subtree height. -/
  rank : Array Nat := #[]
  /-- Reverse map: node index → composite key. -/
  nodeToKey : Array EqKey := #[]

namespace EquivManager

def empty : EquivManager := {}

instance : Inhabited EquivManager := ⟨empty⟩

/-- Reset all equivalence information. -/
def clear (_ : EquivManager) : EquivManager := {}

/-- Get or create a node index for a composite key. -/
def nodeForKey (em : EquivManager) (key : EqKey) : Nat × EquivManager :=
  match em.keyToNode[key]? with
  | some node => (node, em)
  | none =>
    let node := em.parent.size
    (node, { em with
      parent := em.parent.push node
      rank := em.rank.push 0
      nodeToKey := em.nodeToKey.push key
      keyToNode := em.keyToNode.insert key node })

/-- Find root with path halving (every other node → grandparent). A
    well-formed union-find forest reaches a root in fewer than
    `parent.size` hops; the explicit bound replaces the proof-opaque loop.
    The zero branch is reachable only for a malformed cyclic table. -/
def find (em : EquivManager) (node : Nat) : Nat × EquivManager :=
  let (root, parent) := go em.parent node em.parent.size
  (root, { em with parent })
where
  go (parent : Array Nat) (n : Nat) : Nat → Nat × Array Nat
    | 0 => (n, parent)
    | fuel + 1 =>
      if parent[n]! != n then
        let parent := parent.set! n parent[parent[n]!]!
        let n := parent[n]!
        go parent n fuel
      else
        (n, parent)

/-- Union by rank. Returns `true` if the sets were different. -/
def union (em : EquivManager) (a b : Nat) : Bool × EquivManager := Id.run do
  let (ra, em) := em.find a
  let (rb, em) := em.find b
  if ra == rb then
    return (false, em)
  if em.rank[ra]! < em.rank[rb]! then
    return (true, { em with parent := em.parent.set! ra rb })
  else if em.rank[ra]! > em.rank[rb]! then
    return (true, { em with parent := em.parent.set! rb ra })
  else
    return (true, { em with
      parent := em.parent.set! rb ra
      rank := em.rank.set! ra (em.rank[ra]! + 1) })

/-- Check if two composite keys are equivalent. -/
def isEquiv (em : EquivManager) (k1 k2 : EqKey) : Bool × EquivManager :=
  if k1 == k2 then (true, em)
  else match em.keyToNode[k1]?, em.keyToNode[k2]? with
    | some n1, some n2 =>
      let (r1, em) := em.find n1
      let (r2, em) := em.find n2
      (r1 == r2, em)
    | _, _ => (false, em)

/-- Root representative key for a composite key; `none` if absent. -/
def findRootKey (em : EquivManager) (key : EqKey) :
    Option EqKey × EquivManager :=
  match em.keyToNode[key]? with
  | none => (none, em)
  | some node =>
    let (root, em) := em.find node
    (em.nodeToKey[root]?, em)

/-- Record that two composite keys are definitionally equal. -/
def addEquiv (em : EquivManager) (k1 k2 : EqKey) : EquivManager :=
  let (n1, em) := em.nodeForKey k1
  let (n2, em) := em.nodeForKey k2
  (em.union n1 n2).2

end EquivManager

end Ix.Tc

end
end
