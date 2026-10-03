/-! SCC split whose evaporated nested aux is an external MUTUAL family
(aux_gen.rs:1267-1277: multi-motive external target, "outside the supported
rewrite domain; skipping leaves the original compile"). -/
namespace NestMutExtA
mutual
inductive E1 (α : Type)
  | mk : E2 α → E1 α
inductive E2 (α : Type)
  | nil : E2 α
  | cons : α → E1 α → E2 α
end

mutual
inductive A
  | mk : E1 B → A
inductive B
  | leaf
end

def A.isMk : A → Bool
  | .mk _ => true
end NestMutExtA
