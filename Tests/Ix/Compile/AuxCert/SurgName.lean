/-! Surgery H4: a user constant named `A.below` (not an auxiliary: the block
is not recursive, so Lean generates no `.below`) gets the `.below` call-site
plan of a non-identity block layout (compile.rs ~4880). -/
namespace SurgName
mutual
inductive A
  | a : A
inductive B
  | b : B
end

def A.below (x _y : Nat) : Nat := x
theorem A.below_eq : A.below 1 2 = 1 := rfl

def B.brecOn (x _y : Nat) : Nat := x
theorem B.brecOn_eq : B.brecOn 3 4 = 3 := rfl
end SurgName
