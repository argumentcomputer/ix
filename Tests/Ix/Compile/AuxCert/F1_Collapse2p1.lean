/-! F1 (class B, meta ingress): two members alpha-equivalent through a third.
`ix compile F1_Collapse2p1.lean --no-build --consts A,B,C --out c.ixe`
`ix check-rs c.ixe` -> `A: ctor return type: head is not the inductive` (0/9)
`ix check-rs --anon c.ixe` 6/6; `ix check-lean c.ixe` -> `C.n: unknown constant 2f6342baee0d`;
`ix check-lean --anon` 6/6; kernel-check-ixe accepts every record.
Neighbours that pass: the 2-member pair alone (A ↔ B), the 3-ring, the alpha triple. -/
mutual
inductive A where
  | z
  | s : C → A
inductive B where
  | z
  | s : C → B
inductive C where
  | n : A → B → C
  | e
end
