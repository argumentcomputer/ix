/-! Surgery H5: a recursive field hidden behind a reducible alias; the
split-minor adapter detects recursive fields syntactically. -/
namespace SurgAlias
abbrev Id' (α : Type) : Type := α

mutual
inductive A
  | nil : A
  | a : Id' B → A
inductive B
  | nil : B
  | b : B → B
end

noncomputable def f : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1)

theorem f1 : f (.a (.b .nil)) = 2 := rfl
end SurgAlias
