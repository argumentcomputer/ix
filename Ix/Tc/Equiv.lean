module

public import Ix.Address

/-!
Mirror: crates/kernel/src/equiv.rs

Union-find (disjoint set) for context-aware definitional-equality caching:
weighted quick-union with path halving, keyed by `(expr_hash, ctx_hash)`
content-address pairs.

Pure port: operations return the updated manager (path halving mutates on
reads). Do not reuse the `IO.Ref`-based `Ix.UnionFind`.
-/

public section
@[expose] section

namespace Ix.Tc

/-- Composite key: (expression content hash, context content hash). -/
abbrev EqKey := Address × Address

/-- Union-find for tracking definitional equality between
    `(expr_hash, ctx_hash)` pairs. -/
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

/-- Find root with path halving (every other node → grandparent). -/
def find (em : EquivManager) (node : Nat) : Nat × EquivManager := Id.run do
  let mut parent := em.parent
  let mut n := node
  while parent[n]! != n do
    parent := parent.set! n parent[parent[n]!]!
    n := parent[n]!
  return (n, { em with parent })

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
