/-! F8 (class A, whole file, deterministic): the Prop analogue of F2. A mutual Prop block that the
SCC pass splits, with a nested occurrence (through a Prop container) evaporating out of it.
`ix compile F8_PropSplitNested.lean --no-build` -> exit 1. The root failure is `B.below`, whose
original-form compile reads `A.below_1` from the other SCC:
  [ungrounded] B.below: missing constant: A.below_1 (from compile_mutual @ preseed(Const))
Under the one readiness rule (both compilers) the blocks that read `B.below` fail with it
(`A.below_1`, then `A.below`, `A.brecOn`, `A.brecOn_1`, ...; 15 names). Before that rule,
`A.below_1` was published from the provisional aux publication although it references the
failed `B.below`, and the listed failure was `A.brecOn_1`'s own:
  block FAILED A.brecOn_1 (1 members): invalid mutual block: head-rewrite for 'A.rec_1':
  source recursor has no elimination level
Passes when B also references A (`| s : A → B`: no split). Lean accepts the file. -/
inductive PBox (p : Prop) : Prop
  | mk : p → PBox p
mutual
inductive A : Prop
  | mk : PBox B → A
inductive B : Prop
  | leaf
end
