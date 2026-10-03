/-! L2 (code-review lead "PropSplit"/"Coind", generalised; class B, both kernels).
Fails (users rejected: `universe param count: expected 1, got 0`): independent one-constructor
Prop members whose fields are all proofs (with or without fields), an identical pair of such,
and mutual `coinductive` blocks that are alpha-equal or independent.
Passes: independent members with two constructors, with a data field, Eq-like, recursive,
identical two-constructor or indexed pairs, a 3-member block split 2+1, Type/Sort versions. -/
mutual
inductive A : Prop
  | mk : True → A
inductive B : Prop
  | mk : True → True → B
end
theorem ua (h : A) : True := by
  cases h <;> trivial
