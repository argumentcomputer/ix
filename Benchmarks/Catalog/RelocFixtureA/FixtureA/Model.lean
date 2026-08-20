module

@[expose] public section

namespace Collision

inductive Tree (α : Type u) where
  | leaf (value : α)
  | branch (left right : Tree α)

mutual
  inductive Rose (α : Type u) where
    | node (value : α) (children : Grove α)

  inductive Grove (α : Type u) where
    | empty
    | more (head : Rose α) (tail : Grove α)
end

structure Box (α : Type u) where
  payload : α
  copies : Nat

class Marker (α : Type u) where
  mark : α → Nat

axiom seed : Nat

noncomputable def chosen : Nat := Classical.choice (show Nonempty Nat from inferInstance)

meta def metaTag : String := "A-meta"

end Collision
