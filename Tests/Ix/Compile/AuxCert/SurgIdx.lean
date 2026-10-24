/-! Surgery H2: block-wide `n_indices` (taken from the first `X.rec`) used to
slice `.brecOn` call sites of a member with a different index count. -/
namespace SurgIdx
mutual
inductive A : Nat → Type
  | mk : A 0
inductive B : Type
  | leaf : B
  | node : B → B
end

def B.size : B → Nat
  | .leaf => 0
  | .node b => b.size + 1

theorem bsize : B.size (.node .leaf) = 1 := rfl
end SurgIdx

namespace SurgIdx2
mutual
inductive A : Type
  | mk : A
inductive B : Nat → Type
  | leaf : B 0
  | node {n : Nat} : B n → B (n + 1)
end

def B.size : {n : Nat} → B n → Nat
  | _, .leaf => 0
  | _, .node b => b.size + 1

theorem bsize : B.size (.node .leaf) = 1 := rfl
end SurgIdx2
