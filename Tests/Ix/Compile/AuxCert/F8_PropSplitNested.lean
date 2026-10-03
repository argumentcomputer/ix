/-! F8 (class A, whole file, deterministic): the Prop analogue of F2. A mutual Prop block that the
SCC pass splits, with a nested occurrence (through a Prop container) evaporating out of it.
`ix compile F8_PropSplitNested.lean --no-build` -> exit 1:
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
