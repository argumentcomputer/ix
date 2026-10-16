/-! F4 (class B, both kernels): a nested alpha-collapsing pair; constants that USE the
collapsed recursor without its full argument list are ill-typed after compilation.
`ix compile F4_NestedAlphaUsers.lean --no-build --out na.ixe`
`ix check-rs na.ixe --ns A,B,r,t,sizeL,sizeLA` -> 79/84:
  ✗ r: AppTypeMismatch            (unapplied `@A.rec`; also `@A.brecOn`, `@A.rec_1`)
  ✗ A.size._unsafe_rec, B.size._unsafe_rec, sizeL._unsafe_rec, sizeLA._unsafe_rec: AppTypeMismatch
kernel-check-ixe (certified) rejects `r`, `@A.brecOn`, `@A.rec_1` users with "application type mismatch"
(the `_unsafe_rec` ones are unsafe and declined there).
Passes: `t` (fully applied A.rec), A.size/B.size themselves, and the same users on a NON-nested
alpha pair (A | z | s : B → A, B | z | s : A → B). -/
mutual
inductive A : Type where
  | leaf
  | node : List B → A
inductive B : Type where
  | leaf
  | node : List A → B
end
noncomputable def r := @A.rec
theorem t (a : A) : True :=
  A.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True) (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    trivial (fun _ _ => trivial) trivial (fun _ _ => trivial) trivial (fun _ _ _ _ => trivial) trivial (fun _ _ _ _ => trivial) a
mutual
def A.size : A → Nat
  | .leaf => 1
  | .node bs => sizeL bs + 1
def B.size : B → Nat
  | .leaf => 1
  | .node as => sizeLA as + 1
def sizeL : List B → Nat
  | [] => 0
  | b :: bs => b.size + sizeL bs
def sizeLA : List A → Nat
  | [] => 0
  | a :: as => a.size + sizeLA as
end
