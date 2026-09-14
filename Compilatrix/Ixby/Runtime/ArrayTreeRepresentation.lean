import Compilatrix.Ixby.Runtime.Representation

/-! Sparse immutable trees have an exact power-of-two capacity. Their slots
may contain arbitrary Ixby values, including constructors and closures. An
array relates only its live prefix to source elements; unused slots remain
unobservable, which also permits later pop and overwrite operations. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees

open Ix.Ixby Representation

structure Layout where
  empty : CtorId
  leaf : CtorId
  node : CtorId
  array : CtorId
  bytes : CtorId
  rope : CtorId

inductive Tree : Nat → Type
  | empty (height : Nat) : Tree height
  | leaf (value : Value) : Tree 0
  | node {height : Nat} (left right : Tree height) : Tree (height + 1)

def Tree.encode (layout : Layout) : {height : Nat} → Tree height → Value
  | _, .empty _ => .ctor layout.empty #[]
  | _, .leaf value => .ctor layout.leaf #[value]
  | _, .node left right => .ctor layout.node #[left.encode layout, right.encode layout]

def Tree.get : {height : Nat} → Tree height → Nat → Option Value
  | _, .empty _, _ => none
  | _, .leaf value, _ => some value
  | height + 1, .node left right, index =>
      if index < 2 ^ height then left.get index else right.get (index - 2 ^ height)

def Tree.left : Tree (height + 1) → Tree height
  | .empty _ => .empty height
  | .node left _ => left

def Tree.right : Tree (height + 1) → Tree height
  | .empty _ => .empty height
  | .node _ right => right

def Tree.set : (height : Nat) → Tree height → Nat → Value → Tree height
  | 0, _, _, value => .leaf value
  | height + 1, tree, index, value =>
      if index < 2 ^ height then
        .node (tree.left.set height index value) tree.right
      else .node tree.left (tree.right.set height (index - 2 ^ height) value)

@[simp] theorem pow_half (height : Nat) : 2 ^ (height + 1) / 2 = 2 ^ height := by
  rw [Nat.pow_succ, Nat.mul_div_left _ (by decide)]

theorem pow_positive (height : Nat) : 0 < 2 ^ height := Nat.two_pow_pos height

theorem get_children (tree : Tree (height + 1)) (index : Nat) :
    tree.get index = if index < 2 ^ height then tree.left.get index
      else tree.right.get (index - 2 ^ height) := by
  cases tree <;> simp [Tree.get, Tree.left, Tree.right]

/-- Writing a slot changes that slot alone, even when the old subtree is empty. -/
theorem Tree.get_set (height : Nat) (tree : Tree height) (index query : Nat) (value : Value)
    (indexBound : index < 2 ^ height) (queryBound : query < 2 ^ height) :
    (tree.set height index value).get query =
      if query = index then some value else tree.get query := by
  induction height generalizing index query with
  | zero =>
    have : index = 0 ∧ query = 0 := by simpa using And.intro indexBound queryBound
    simp [Tree.set, Tree.get, this.1, this.2]
  | succ height ih =>
    have positive := pow_positive height
    have capacity : 2 ^ (height + 1) = 2 ^ height + 2 ^ height := by
      rw [Nat.pow_succ]; omega
    rw [Tree.set, get_children tree query]
    by_cases leftIndex : index < 2 ^ height <;>
      by_cases leftQuery : query < 2 ^ height
    · simp [leftIndex, leftQuery, Tree.get, ih tree.left index query leftIndex leftQuery]
    · have different : query ≠ index := by omega
      simp [leftIndex, leftQuery, Tree.get, different]
    · have different : query ≠ index := by omega
      simp [leftIndex, leftQuery, Tree.get, different]
    · have indexRest : index - 2 ^ height < 2 ^ height := by omega
      have queryRest : query - 2 ^ height < 2 ^ height := by omega
      have same : query - 2 ^ height = index - 2 ^ height ↔ query = index := by omega
      simp [leftIndex, leftQuery, Tree.get,
        ih tree.right (index - 2 ^ height) (query - 2 ^ height) indexRest queryRest, same]

/-- The live prefix is related element by element, without restricting the
representation of source elements. Numeric size may use any valid layout. -/
structure Prefix (numbers : NumberLayout) (element : α → Value → Prop)
    (source : Array α) (height : Nat) (tree : Tree height) (size : Value) : Prop where
  capacity : source.size ≤ 2 ^ height
  sizeRep : Number numbers source.size size
  elements : ∀ index (bound : index < source.size),
    ∃ value, tree.get index = some value ∧ element source[index] value

def arrayValue (layout : Layout) (height : Nat) (tree : Tree height) (size : Value) : Value :=
  .ctor layout.array #[size, .scalar (.nat (2 ^ height)), tree.encode layout]

def Represents (numbers : NumberLayout) (layout : Layout) (element : α → Value → Prop)
    (source : Array α) (value : Value) : Prop :=
  ∃ height tree size, value = arrayValue layout height tree size ∧
    Prefix numbers element source height tree size

theorem empty_prefix (numbers : NumberLayout) (element : α → Value → Prop) :
    Prefix numbers element #[] 0 (.empty 0)
      (.ctor numbers.cached #[.scalar (.nat 0), .scalar (.word32 0)]) := by
  exact ⟨by simp, .cached 0, by simp⟩

end Compilatrix.Ixby.Runtime.ArrayTrees
