/-! CORPUS-IPB (M1-j), the valid neighbour of `IPBCollapse2p1`: the same mutual
`Prop` block without the alpha-equivalent pair (`B` gains a second recursive field,
so no two members are alpha-equivalent and nothing collapses). It compiles, and its
`IndPredBelow` family keeps Lean's types (`ix validate-lean` phase 5). -/
namespace IPBCollapseNone
mutual
inductive A : Prop where
  | z
  | s : C → A

inductive B : Prop where
  | z
  | s : C → C → B

inductive C : Prop where
  | n : A → B → C
  | e
end
end IPBCollapseNone
