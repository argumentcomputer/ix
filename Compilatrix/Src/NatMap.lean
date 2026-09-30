/-! # A persistent `Nat`-keyed map

A binary trie on the key's bits, low bit first (D17: the recheck path uses
persistent `Nat`-keyed maps, not `HashMap`s or array indexing). Every
operation recurses structurally: lookups on the trie, updates on a fuel of
`k + 1` steps for key `k` (each step halves the key and stops at zero, so
the fuel never runs out), so the kernel can evaluate every operation. A node
reached by a nonzero key's bits holds that key's value; the root holds key
0. -/

namespace Compilatrix.Src

inductive NatMap (α : Type) where
  | leaf
  | node (value : Option α) (zero one : NatMap α)
  deriving Inhabited, Repr

namespace NatMap

variable {α β : Type}

def empty : NatMap α := .leaf

/-- The value and children of a node (a leaf is an empty node). -/
def parts : NatMap α → Option α × NatMap α × NatMap α
  | .leaf => (none, .leaf, .leaf)
  | .node v z o => (v, z, o)

def getF : Nat → NatMap α → Nat → Option α
  | _, .leaf, _ => none
  | 0, .node v _ _, _ => v
  | fuel + 1, .node v z o, k =>
    if k == 0 then v
    else if k % 2 == 0 then getF fuel z (k / 2)
    else getF fuel o (k / 2)

/-- The value at key `k` (structural on the trie: each step enters a child,
so no fuel is needed). -/
def get? : NatMap α → Nat → Option α
  | .leaf, _ => none
  | .node v z o, k =>
    if k == 0 then v
    else if k % 2 == 0 then get? z (k / 2)
    else get? o (k / 2)

def setF : Nat → NatMap α → Nat → Option α → NatMap α
  | 0, m, _, x => let (_, z, o) := parts m; .node x z o
  | fuel + 1, m, k, x =>
    let (v, z, o) := parts m
    if k == 0 then .node x z o
    else if k % 2 == 0 then .node v (setF fuel z (k / 2) x) o
    else .node v z (setF fuel o (k / 2) x)

def insert (m : NatMap α) (k : Nat) (x : α) : NatMap α := setF (k + 1) m k (some x)

/-- Remove key `k` (its node stays, empty). -/
def erase (m : NatMap α) (k : Nat) : NatMap α := setF (k + 1) m k none

def getD (m : NatMap α) (k : Nat) (d : α) : α := (m.get? k).getD d

def contains (m : NatMap α) (k : Nat) : Bool := (m.get? k).isSome

/-- Apply `f` to the value at `k`, if any. -/
def modify (m : NatMap α) (k : Nat) (f : α → α) : NatMap α :=
  match m.get? k with
  | some x => m.insert k (f x)
  | none => m

/-- Build from a list of pairs (later pairs win). -/
def ofList (xs : List (Nat × α)) : NatMap α :=
  xs.foldl (fun m (k, x) => m.insert k x) .leaf

/-- The dense map `i ↦ xs[i]`. -/
def ofDense (xs : List α) : NatMap α :=
  ofList (xs.zipIdx.map fun (x, i) => (i, x))

/-- `i ↦ x` for every `some x` at index `i`. -/
def ofOptions (xs : List (Option α)) : NatMap α :=
  ofList (xs.zipIdx.filterMap fun (x, i) => x.map (i, ·))

def map (f : α → β) : NatMap α → NatMap β
  | .leaf => .leaf
  | .node v z o => .node (v.map f) (map f z) (map f o)

/-- The entries prepended to `acc`, for the subtrie whose root holds key
`k` and whose children add bit weight `w`. -/
def entriesAux : NatMap α → Nat → Nat → List (Nat × α) → List (Nat × α)
  | .leaf, _, _, acc => acc
  | .node v z o, k, w, acc =>
    let acc := entriesAux o (k + w) (2 * w) acc
    let acc := entriesAux z k (2 * w) acc
    match v with
    | some x => (k, x) :: acc
    | none => acc

/-- Every entry, in trie order (a node before its zero subtrie, then its one
subtrie); not sorted by key. -/
def toList (m : NatMap α) : List (Nat × α) := entriesAux m 0 1 []

/-- The number of entries. -/
def size : NatMap α → Nat
  | .leaf => 0
  | .node v z o => (if v.isSome then 1 else 0) + size z + size o

end NatMap

/-- A persistent set of `Nat`s (D17). -/
abbrev NatSet := NatMap Unit

namespace NatSet

def insert (s : NatSet) (k : Nat) : NatSet := NatMap.insert s k ()

def ofList (ks : List Nat) : NatSet := NatMap.ofList (ks.map (·, ()))

end NatSet

end Compilatrix.Src
