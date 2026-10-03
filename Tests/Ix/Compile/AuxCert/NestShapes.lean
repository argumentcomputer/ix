/-! H5/H6: nested occurrences under a binder (reflexive-nested) and through an
indexed external family. -/
namespace NestShapes
inductive R
  | leaf
  | mk : (Nat → List R) → R

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

inductive T
  | leaf
  | mk : Vec T 2 → T

end NestShapes
