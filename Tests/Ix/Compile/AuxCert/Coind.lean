/-! Lean 4.34 `coinductive`: elaborated as "flat" `_functor` inductives
(MutualInductive.mkFlatInductive) that get mkAuxConstructions. A mutual
coinductive gives a mutual inductDecl whose members do not reference each
other (Lean splits nothing; aux-gen's SCC split does). -/
namespace Coind
coinductive InfSeq (r : Nat → Nat → Prop) : Nat → Prop where
  | step {a b : Nat} : r a b → InfSeq r b → InfSeq r a

mutual
coinductive Ev : Nat → Prop where
  | s {n : Nat} : Od n → Ev (n + 1)
coinductive Od : Nat → Prop where
  | s {n : Nat} : Ev n → Od (n + 1)
end

mutual
coinductive CA : Prop where
  | mk : CB → CA
coinductive CB : Prop where
  | mk : CA → CB
end
end Coind
