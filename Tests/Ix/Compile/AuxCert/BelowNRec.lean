/-! A nested Prop inductive: Lean's `IndPredBelow` family has a member for
the auxiliary, `P.below_1`, whose recursor `P.below_1.rec` is its own
strongly connected component. -/
namespace BelowNRec
inductive Q (α : Prop) : Prop
  | mk : α → Q α

inductive P : Prop
  | leaf : P
  | node : Q P → P
end BelowNRec
