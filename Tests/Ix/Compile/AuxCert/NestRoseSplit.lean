/-! SCC split whose evaporated nested aux is an external NESTED type
(Rose.rec has two motives). -/
namespace NestRoseSplit
inductive Rose (α : Type)
  | node : α → List (Rose α) → Rose α

mutual
inductive A2
  | mk : Rose B2 → A2
inductive B2
  | leaf
end

def A2.isMk : A2 → Bool
  | .mk _ => true
end NestRoseSplit
