/-
  EquivManager: Union-find based equivalence tracking for definitional equality.

  Ported from lean4lean's EquivManager. Provides structural expression walking
  with union-find to recognize congruence: if a ~ b and c ~ d, then f a c ~ f b d
  is detected without re-entering isDefEq.
-/
import Batteries.Data.UnionFind.Basic
import Ix.Kernel.Datatypes

namespace Ix.Kernel

abbrev NodeRef := Nat

structure EquivManager (m : MetaMode) where
  uf        : Batteries.UnionFind := {}
  toNodeMap : Std.HashMap (Expr m) NodeRef := {}

instance : Inhabited (EquivManager m) := ⟨{}⟩

namespace EquivManager

/-- Map an expression to a union-find node, creating one if it doesn't exist. -/
def toNode (e : Expr m) : StateM (EquivManager m) NodeRef := fun mgr =>
  match mgr.toNodeMap.get? e with
  | some n => (n, mgr)
  | none =>
    let n := mgr.uf.size
    (n, { uf := mgr.uf.push, toNodeMap := mgr.toNodeMap.insert e n })

/-- Find the root of a node with path compression. -/
def find (n : NodeRef) : StateM (EquivManager m) NodeRef := fun mgr =>
  let (uf', root) := mgr.uf.findD n
  (root, { mgr with uf := uf' })

/-- Merge two nodes into the same equivalence class. -/
def merge (n1 n2 : NodeRef) : StateM (EquivManager m) Unit := fun mgr =>
  if n1 < mgr.uf.size && n2 < mgr.uf.size then
    ((), { mgr with uf := mgr.uf.union! n1 n2 })
  else
    ((), mgr)

/-- Check structural equivalence with union-find memoization.
    Recursively walks expression structure, checking if corresponding
    sub-expressions are in the same union-find equivalence class.
    Merges nodes on success for future O(α(n)) lookups.

    When `useHash = true`, expressions with different hashes are immediately
    rejected without structural walking (fast path for obviously different terms). -/
partial def isEquiv (useHash : Bool) (e1 e2 : Expr m) : StateM (EquivManager m) Bool := do
  -- 1. Pointer/structural equality (O(1) via Blake3 content-addressing)
  if e1 == e2 then return true
  -- 2. Hash mismatch → definitely not structurally equal
  if useHash && Hashable.hash e1 != Hashable.hash e2 then return false
  -- 3. BVar fast path (compare indices directly, don't add to union-find)
  match e1, e2 with
  | .bvar i _, .bvar j _ => return i == j
  | _, _ => pure ()
  -- 4. Union-find root comparison
  let r1 ← find (← toNode e1)
  let r2 ← find (← toNode e2)
  if r1 == r2 then return true
  -- 5. Structural decomposition
  let result ← match e1, e2 with
    | .const a1 l1 _, .const a2 l2 _ => pure (a1 == a2 && l1 == l2)
    | .sort l1, .sort l2 => pure (l1 == l2)
    | .lit l1, .lit l2 => pure (l1 == l2)
    | .app f1 a1, .app f2 a2 =>
      if ← isEquiv useHash f1 f2 then isEquiv useHash a1 a2 else pure false
    | .lam d1 b1 _ _, .lam d2 b2 _ _ =>
      if ← isEquiv useHash d1 d2 then isEquiv useHash b1 b2 else pure false
    | .forallE d1 b1 _ _, .forallE d2 b2 _ _ =>
      if ← isEquiv useHash d1 d2 then isEquiv useHash b1 b2 else pure false
    | .proj ta1 i1 s1 _, .proj ta2 i2 s2 _ =>
      if ta1 == ta2 && i1 == i2 then isEquiv useHash s1 s2 else pure false
    | .letE t1 v1 b1 _, .letE t2 v2 b2 _ =>
      if ← isEquiv useHash t1 t2 then
        if ← isEquiv useHash v1 v2 then isEquiv useHash b1 b2 else pure false
      else pure false
    | _, _ => pure false
  -- 6. Merge on success
  if result then merge r1 r2
  return result

/-- Directly merge two expressions into the same equivalence class. -/
def addEquiv (e1 e2 : Expr m) : StateM (EquivManager m) Unit := do
  let r1 ← find (← toNode e1)
  let r2 ← find (← toNode e2)
  merge r1 r2

end EquivManager
end Ix.Kernel
