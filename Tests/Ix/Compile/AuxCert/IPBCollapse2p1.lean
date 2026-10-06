/-! CORPUS-IPB (M1-j): a mutual `Prop` block in which two of three members are
alpha-equivalent (`A`, `B`; the corpus shape `M3_P_alpha2p1`). The default path
collapses `A`/`B`, and before the refusal it stored the Lean-named `IndPredBelow`
constructors of the non-representative member with the representative's motive
(`A.below.z : A.below motive_2 motive_2 motive_3 A.z`, Lean's
`A.below motive_1 motive_2 motive_3 A.z`). Both compilers now refuse the block
(`REFUSED-IPB-COLLAPSE`). Neighbours: `IPBCollapseNone` (the same block without the
alpha-equivalent pair), `F1_Collapse2p1` (the `Type` version, which compiles). -/
namespace IPBCollapse2p1
mutual
inductive A : Prop where
  | z
  | s : C → A

inductive B : Prop where
  | z
  | s : C → B

inductive C : Prop where
  | n : A → B → C
  | e
end
end IPBCollapse2p1
