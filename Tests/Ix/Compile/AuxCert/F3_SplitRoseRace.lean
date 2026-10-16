/-! F3 (classes A and B, whole file, nondeterministic).
`ix compile F3_SplitRoseRace.lean --no-build` fails ~1 run in 4:
  block FAILED A.below_2 (1 members): missing constant: A.rec_1 (from A.below_2 @ compile_expr(Const))
  (then A.brecOn_2(.go), A.brecOn_1(.go): missing constant: A.below_2)
Successful runs are byte-identical, and `ix check-rs` rejects them:
  A.rec_2: kernel: universe param count: expected 1, got 2 -/
inductive Rose (α : Type)
  | node : α → List (Rose α) → Rose α
mutual
inductive A
  | mk : Rose B → A
inductive B
  | leaf
end
