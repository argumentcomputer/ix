/-! A0 (WB-A1; a1c item 7): a nested occurrence through an EXTERNAL MUTUAL
family. Lean's kernel (`elim_nested_inductive_fn`) registers every member of
the external group when it first sees one, so `T` has exactly two nested
auxiliaries, in group order: `T.rec_1` for `Tree T` and `T.rec_2` for
`Forest T`. Both Ix ports used to register only the triggering member, built
four auxiliaries and rejected the block (`numNested` 2 vs 4). -/
namespace NestMutGroup
mutual
inductive Tree (α : Type) where
  | node : α → Forest α → Tree α
inductive Forest (α : Type) where
  | nil : Forest α
  | cons : Tree α → Forest α → Forest α
end

inductive T where
  | leaf : T
  | mk : Tree T → T

/-- Counts leaves through the nested recursor (motives in Lean's order:
    `T`, `Tree T`, `Forest T`). -/
noncomputable def leaves : T → Nat :=
  @T.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    1 (fun _ ih => ih)
    (fun _ _ ihx ihf => ihx + ihf)
    0 (fun _ _ iht ihf => iht + ihf)

theorem leaves_pin :
    leaves (.mk (.node .leaf (.cons (.node .leaf .nil) .nil))) = 2 := rfl
end NestMutGroup
