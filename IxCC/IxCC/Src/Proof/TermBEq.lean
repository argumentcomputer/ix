import IxCC.Src.Syntax

/-! # `Term`'s derived `BEq` is lawful

`Src.Term` and the types of its fields derive `BEq` (not `DecidableEq`), so `t == u` does not
give `t = u` by itself. The instances below make the derived comparisons lawful; they are the
deriving handler's, on the instances the types already derive (`Univ`, `PropWhen`, `Rel`, `Mode`,
`Binder`, `LetContract`, `Term`; `BinderContract` and `ValueContract` have theirs in
`Ixon.V3.Contracts`). `Relevance.Proof.Canonical` keeps its own file-local instances for `PropWhen`,
`Rel` and `FieldClass`; the two coexist (they are proofs of the same `Prop`). -/

namespace IxCC.Src.Proof

deriving instance ReflBEq, LawfulBEq for IxCC.Ixon.Univ
deriving instance ReflBEq, LawfulBEq for IxCC.Src.PropWhen
deriving instance ReflBEq, LawfulBEq for IxCC.Src.Rel
deriving instance ReflBEq, LawfulBEq for IxCC.Src.Mode
deriving instance ReflBEq, LawfulBEq for IxCC.Src.Binder
deriving instance ReflBEq, LawfulBEq for IxCC.Ixon.V3.LetContract
deriving instance ReflBEq, LawfulBEq for IxCC.Src.Term

/-- `==` on terms is equality. -/
theorem term_eq_of_beq {t u : Term} (h : (t == u) = true) : t = u := eq_of_beq h

end IxCC.Src.Proof
