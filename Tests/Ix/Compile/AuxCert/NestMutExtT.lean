/-! Nested through an external mutual family (only this). -/
namespace NestMutExtT
mutual
inductive E1 (α : Type)
  | mk : E2 α → E1 α
inductive E2 (α : Type)
  | nil : E2 α
  | cons : α → E1 α → E2 α
end

inductive T
  | leaf
  | mk : E1 T → T
end NestMutExtT
