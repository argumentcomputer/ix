module

public import FixtureB.Model

@[expose] public section

namespace Collision

def tag : String := "B"

def Tree.size : Tree α → Nat
  | .leaf _ => 2
  | .branch left right => left.size + right.size + 10

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf value => .leaf (f value)
  | .branch left right => .branch (left.map f) (right.map f)

mutual
  def evenCode : Nat → Nat
    | 0 => 20
    | n + 1 => oddCode n

  def oddCode : Nat → Nat
    | 0 => 21
    | n + 1 => evenCode n
end

partial def partialCode : Nat → Nat
  | 0 => 22
  | n + 1 => partialCode n

def Box.weight (box : Box α) : Nat := box.copies + 20

instance : Marker Nat where
  mark n := n + 200

theorem Tree.size_leaf (value : α) : (Tree.leaf value).size = 2 := rfl

end Collision
