/-! F2 (classes A, B, C; closure mode only): SCC split, nested occurrence evaporates.
Whole file: compiles, check-rs 40/40.
`ix compile F2_SplitNestedClosure.lean --no-build --consts A` -> block FAILED A (2 members):
  invalid mutual block: conflicting call-site plans for 'A.rec_1' — two blocks claim one source-indexed aux name
`--consts A.rec` (also A.casesOn, A.below, B.rec, A.rec_1): compiles; A.rec_1 address differs from the
whole compile (efcb43e4… vs 41369b84…) and `ix check-rs` rejects it:
  populate_recursor_rules_from_block: canonical header mismatch at peer 0
Same with Tri/Rose/E1 (any container) in place of List. -/
mutual
inductive A
  | mk : List B → A
inductive B
  | leaf
end
