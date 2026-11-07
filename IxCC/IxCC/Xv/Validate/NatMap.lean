/-!
# A persistent map keyed by `Nat`, for kernel evaluation

The validator runs on `Recheck.run`'s path, which Lean's kernel must be able
to evaluate (roadmap D17): no `HashMap`, no `Array` indexing (a list walk in
the kernel), no well-founded recursion. This is a binary trie on the
bijective base-2 digits of the key: key `0` sits at a node, and key `2m + 1`
(`2m + 2`) lives at key `m` of the left (right) child. Lookups recurse
structurally on the trie; updates recurse on a fuel of `k + 1`, which always
exceeds the depth `⌊log₂ (k + 1)⌋`. The kernel's `Nat` literals make `k % 2`
and `k / 2` single steps, so a lookup or update costs `O(log k)`.

Empty subtries are pruned, so a map has one representation per content
(structural equality is extensional equality).
-/

namespace IxCC.Xv.Validate

inductive NatMap (α : Type) where
  | leaf
  | node (v : Option α) (l r : NatMap α)
  deriving DecidableEq, Repr, Inhabited

namespace NatMap

variable {α β : Type}

def empty : NatMap α := .leaf

/-- A node, pruned to `leaf` when it holds nothing. -/
def mk : Option α → NatMap α → NatMap α → NatMap α
  | none, .leaf, .leaf => .leaf
  | v, l, r => .node v l r

def find? : NatMap α → Nat → Option α
  | .leaf, _ => none
  | .node v l r, k =>
      if k == 0 then v
      else if k % 2 == 1 then find? l (k / 2)
      else find? r (k / 2 - 1)

/-- Replace the entry at `k` by `f` of the current one; `fuel` bounds the
depth. -/
def alterAux (f : Option α → Option α) : (fuel : Nat) → NatMap α → Nat → NatMap α
  | 0, m, _ => m
  | fuel + 1, m, k =>
      match m with
      | .leaf =>
          if k == 0 then mk (f none) .leaf .leaf
          else if k % 2 == 1 then mk none (alterAux f fuel .leaf (k / 2)) .leaf
          else mk none .leaf (alterAux f fuel .leaf (k / 2 - 1))
      | .node v l r =>
          if k == 0 then mk (f v) l r
          else if k % 2 == 1 then mk v (alterAux f fuel l (k / 2)) r
          else mk v l (alterAux f fuel r (k / 2 - 1))

def alter (m : NatMap α) (k : Nat) (f : Option α → Option α) : NatMap α := alterAux f (k + 1) m k

def insert (m : NatMap α) (k : Nat) (a : α) : NatMap α := m.alter k fun _ => some a

def erase (m : NatMap α) (k : Nat) : NatMap α := m.alter k fun _ => none

/-! Traversals see each entry with its key. The digits of a key are read
least significant first, so a node at depth `d` with key `k` has children
with keys `k + 2^d` (left) and `k + 2^(d+1)` (right); `pow` is `2^d`. -/

/-- Entries with their keys, in trie order. -/
def foldAux (f : β → Nat → α → β) : NatMap α → Nat → Nat → β → β
  | .leaf, _, _, b => b
  | .node v l r, key, pow, b =>
      let b := match v with
        | some a => f b key a
        | none => b
      foldAux f r (key + 2 * pow) (2 * pow) (foldAux f l (key + pow) (2 * pow) b)

def fold (f : β → Nat → α → β) (init : β) (m : NatMap α) : β := foldAux f m 0 1 init

def toList (m : NatMap α) : List (Nat × α) := (m.fold (fun acc k a => (k, a) :: acc) []).reverse

def size (m : NatMap α) : Nat := m.fold (fun n _ _ => n + 1) 0

/-- Whether every entry satisfies `p`. -/
def allAux (p : Nat → α → Bool) : NatMap α → Nat → Nat → Bool
  | .leaf, _, _ => true
  | .node v l r, key, pow =>
      (match v with | some a => p key a | none => true) &&
        allAux p l (key + pow) (2 * pow) && allAux p r (key + 2 * pow) (2 * pow)

def all (m : NatMap α) (p : Nat → α → Bool) : Bool := allAux p m 0 1

/-- Map every entry, dropping those sent to `none`. -/
def filterMapAux (f : Nat → α → Option β) : NatMap α → Nat → Nat → NatMap β
  | .leaf, _, _ => .leaf
  | .node v l r, key, pow =>
      mk (v.bind (f key)) (filterMapAux f l (key + pow) (2 * pow)) (filterMapAux f r (key + 2 * pow) (2 * pow))

def filterMap (m : NatMap α) (f : Nat → α → Option β) : NatMap β := filterMapAux f m 0 1

def ofList (xs : List (Nat × α)) : NatMap α := xs.foldl (fun m (k, a) => m.insert k a) .leaf

end NatMap

end IxCC.Xv.Validate
