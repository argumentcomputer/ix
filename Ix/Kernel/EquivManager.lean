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
  nodeToPtr : Array USize := #[]  -- reverse map: node index → pointer address

instance : Inhabited EquivManager := ⟨{}⟩

namespace EquivManager

/-- Map a pointer address to a union-find node, creating one if it doesn't exist. -/
def toNode (ptr : USize) : StateM EquivManager NodeRef := fun mgr =>
  match mgr.toNodeMap.get? ptr with
  | some n => (n, mgr)
  | none =>
    let n := mgr.uf.size
    (n, { uf := mgr.uf.push, toNodeMap := mgr.toNodeMap.insert ptr n,
          nodeToPtr := mgr.nodeToPtr.push ptr })

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

/-- Find the canonical (root) pointer for a given pointer's equivalence class.
    Returns none if the pointer has never been registered. -/
def findRootPtr (ptr : USize) : StateM EquivManager (Option USize) := fun mgr =>
  match mgr.toNodeMap.get? ptr with
  | none => (none, mgr)
  | some n =>
    let (uf', root) := mgr.uf.findD n
    let mgr' := { mgr with uf := uf' }
    if h : root < mgr'.nodeToPtr.size then
      (some mgr'.nodeToPtr[root], mgr')
    else
      (some ptr, mgr')  -- shouldn't happen, fallback to self

/-- Check equivalence without creating nodes for unknown pointers. -/
def tryIsEquiv (ptr1 ptr2 : USize) : StateM EquivManager Bool := fun mgr =>
  if ptr1 == ptr2 then (true, mgr)
  else match mgr.toNodeMap.get? ptr1, mgr.toNodeMap.get? ptr2 with
    | some n1, some n2 =>
      let (uf', r1) := mgr.uf.findD n1
      let (uf'', r2) := uf'.findD n2
      (r1 == r2, { mgr with uf := uf'' })
    | _, _ => (false, mgr)

end EquivManager
end Ix.Kernel
