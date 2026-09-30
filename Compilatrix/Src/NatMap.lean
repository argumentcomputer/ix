/-! # A persistent `Nat`-keyed map

A binary trie on the key's bits, low bit first (D17: the recheck path uses
persistent `Nat`-keyed maps, not `HashMap`s or array indexing). Every
operation recurses structurally on a fuel of `k + 1` steps for key `k`; each
step halves the key and stops at zero, so the fuel never runs out and the
kernel can evaluate every operation. -/

namespace Compilatrix.Src

inductive NatMap (α : Type) where
  | leaf
  | node (value : Option α) (zero one : NatMap α)
  deriving Inhabited

namespace NatMap

variable {α : Type}

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

def get? (m : NatMap α) (k : Nat) : Option α := getF (k + 1) m k

def setF : Nat → NatMap α → Nat → Option α → NatMap α
  | 0, m, _, x => let (_, z, o) := parts m; .node x z o
  | fuel + 1, m, k, x =>
    let (v, z, o) := parts m
    if k == 0 then .node x z o
    else if k % 2 == 0 then .node v (setF fuel z (k / 2) x) o
    else .node v z (setF fuel o (k / 2) x)

def insert (m : NatMap α) (k : Nat) (x : α) : NatMap α := setF (k + 1) m k (some x)

def getD (m : NatMap α) (k : Nat) (d : α) : α := (m.get? k).getD d

def contains (m : NatMap α) (k : Nat) : Bool := (m.get? k).isSome

/-- Build from a list of pairs (later pairs win). -/
def ofList (xs : List (Nat × α)) : NatMap α :=
  xs.foldl (fun m (k, x) => m.insert k x) .leaf

end NatMap

end Compilatrix.Src
