/-
  Kernel2 EquivManager: Pointer-address-based union-find for Val def-eq caching.

  Unlike Kernel1's Expr-based EquivManager which does structural congruence walking,
  this version uses pointer addresses (USize) as keys. Within a single checkConst
  session, Lean's reference-counting GC ensures addresses are stable.

  Provides transitivity: if a =?= b and b =?= c succeed, then a =?= c is O(α(n)).
-/
import Batteries.Data.UnionFind.Basic

namespace Ix.Kernel

abbrev NodeRef := Nat

structure EquivManager where
  uf        : Batteries.UnionFind := {}
  toNodeMap : Std.TreeMap USize NodeRef compare := {}

instance : Inhabited EquivManager := ⟨{}⟩

namespace EquivManager

/-- Map a pointer address to a union-find node, creating one if it doesn't exist. -/
def toNode (ptr : USize) : StateM EquivManager NodeRef := fun mgr =>
  match mgr.toNodeMap.get? ptr with
  | some n => (n, mgr)
  | none =>
    let n := mgr.uf.size
    (n, { uf := mgr.uf.push, toNodeMap := mgr.toNodeMap.insert ptr n })

/-- Find the root of a node with path compression. -/
def find (n : NodeRef) : StateM EquivManager NodeRef := fun mgr =>
  let (uf', root) := mgr.uf.findD n
  (root, { mgr with uf := uf' })

/-- Merge two nodes into the same equivalence class. -/
def merge (n1 n2 : NodeRef) : StateM EquivManager Unit := fun mgr =>
  if n1 < mgr.uf.size && n2 < mgr.uf.size then
    ((), { mgr with uf := mgr.uf.union! n1 n2 })
  else
    ((), mgr)

/-- Check if two pointer addresses are in the same equivalence class. -/
def isEquiv (ptr1 ptr2 : USize) : StateM EquivManager Bool := do
  if ptr1 == ptr2 then return true
  let r1 ← find (← toNode ptr1)
  let r2 ← find (← toNode ptr2)
  return r1 == r2

/-- Record that two pointer addresses are definitionally equal. -/
def addEquiv (ptr1 ptr2 : USize) : StateM EquivManager Unit := do
  let r1 ← find (← toNode ptr1)
  let r2 ← find (← toNode ptr2)
  merge r1 r2

end EquivManager
end Ix.Kernel
