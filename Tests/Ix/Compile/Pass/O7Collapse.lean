/- A6p per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O7, `rec`/`recOn` over a collapsed block with identical motives and minors per class. `Src.A`,
`Src.B` are alpha-equivalent (one class). `Src.A.viaRec` and `Src.B.viaRecOn` give both members
the same motive and the same minors (up to the collapse renaming): O7 drops the duplicates and
their canonical forms `Src.A.viaRec._ix`, `Src.B.viaRecOn._ix` (decision 5, D1) are the bytes of
`Can`, where the class is declared once (`X.rec P mins x`); the Lean names keep their baselines
(recorded `PJ-FORM-O7`).
`Src.A.distinct` gives the two members different minors (`SurgCollapse.f`'s shape): O7 declines
and the paired image stays (the pair-valued form is O12's). `Src.Z.viaRec` eliminates a lifted
member (`Z`, a singleton class next to the collapsed `X`, `Y`) with identical arguments for `X`
and `Y`: O7 fires (`Can` declares `X`, `Z`). Value pins by `rfl` over every function. -/
set_option Elab.async false

namespace PassO7
namespace Src
mutual
inductive A
  | a : B → A
  | nil : A
inductive B
  | b : A → B
  | nil : B
end

noncomputable def A.viaRec (x : A) : Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0 x

noncomputable def B.viaRecOn (x : B) : Nat :=
  @B.recOn (fun _ => Nat) (fun _ => Nat) x (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0

noncomputable def A.distinct (x : A) : Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih * 2) 100 x

theorem viaRec_two : A.viaRec (.a (.b .nil)) = 2 := rfl
theorem viaRecOn_one : B.viaRecOn (.b .nil) = 1 := rfl
theorem distinct_one : A.distinct (.a (.b .nil)) = 1 := rfl
theorem distinct_nil : A.distinct .nil = 0 := rfl

mutual
inductive X
  | z : X
  | s : Z → X
inductive Y
  | z : Y
  | s : Z → Y
inductive Z
  | n : X → Y → Z
  | e : Z
end

noncomputable def Z.viaRec (z : Z) : Nat :=
  @Z.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    0 (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) (fun _ _ i j => i + j) 5 z

theorem zviaRec : Z.viaRec (.n (.s .e) .z) = 6 := rfl
end Src

namespace Can
inductive A
  | a : A → A
  | nil : A

noncomputable def A.viaRec (x : A) : Nat :=
  @A.rec (fun _ => Nat) (fun _ ih => ih + 1) 0 x

noncomputable def B.viaRecOn (x : A) : Nat :=
  @A.recOn (fun _ => Nat) x (fun _ ih => ih + 1) 0

theorem viaRec_two : A.viaRec (.a (.a .nil)) = 2 := rfl
theorem viaRecOn_one : B.viaRecOn (.a .nil) = 1 := rfl

mutual
inductive X
  | z : X
  | s : Z → X
inductive Z
  | n : X → X → Z
  | e : Z
end

noncomputable def Z.viaRec (z : Z) : Nat :=
  @Z.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) (fun _ _ i j => i + j) 5 z

theorem zviaRec : Z.viaRec (.n (.s .e) .z) = 6 := rfl
end Can
end PassO7
