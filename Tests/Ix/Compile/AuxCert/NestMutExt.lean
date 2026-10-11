/-! H7: nested through an external MUTUAL family, and the SCC-split
("evaporated aux") case whose external recursor has several motives, which
aux_gen.rs:1267-1277 says is outside the supported rewrite domain. -/
namespace NestMutExt
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

mutual
inductive A
  | mk : E1 B → A
inductive B
  | leaf
end

inductive Rose (α : Type)
  | node : α → List (Rose α) → Rose α

mutual
inductive A2
  | mk : Rose B2 → A2
inductive B2
  | leaf
end

def A.isMk : A → Bool
  | .mk _ => true
end NestMutExt
