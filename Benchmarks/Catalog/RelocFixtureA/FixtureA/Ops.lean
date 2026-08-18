module

public import FixtureA.Model

@[expose] public section

namespace Collision

def tag : String := "A"

def Tree.size : Tree α → Nat
  | .leaf _ => 1
  | .branch left right => left.size + right.size + 1

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf value => .leaf (f value)
  | .branch left right => .branch (left.map f) (right.map f)

mutual
  def evenCode : Nat → Nat
    | 0 => 10
    | n + 1 => oddCode n

  def oddCode : Nat → Nat
    | 0 => 11
    | n + 1 => evenCode n
end

partial def partialCode : Nat → Nat
  | 0 => 12
  | n + 1 => partialCode n

def Box.weight (box : Box α) : Nat := box.copies + 10

instance : Marker Nat where
  mark n := n + 100

theorem Tree.size_leaf (value : α) : (Tree.leaf value).size = 1 := rfl

end Collision
