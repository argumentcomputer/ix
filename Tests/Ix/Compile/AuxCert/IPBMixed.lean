/-! CORPUS-IPB (M1-j): the corpus shape `M4_P_mixed`, a four-member mutual `Prop`
block in which `C` and `D` are alpha-equivalent and the other members are not.
The default path refuses it (`REFUSED-IPB-COLLAPSE`), as `IPBCollapse2p1`. -/
namespace IPBMixed
mutual
inductive A : Prop where
  | z
  | mk : B 0 → D → A

inductive B : Nat → Prop where
  | mk : C → B 0

inductive C : Prop where
  | mk : A → C
  | e

inductive D : Prop where
  | mk : A → D
  | e
end
end IPBMixed
