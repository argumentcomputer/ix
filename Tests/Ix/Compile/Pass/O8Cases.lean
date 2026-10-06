/- A6p per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O8, `casesOn` (and the matchers built on it) over a collapsed or lifted member. `Src.A`, `Src.B`
are alpha-equivalent (one class), so their `casesOn` images are packed; O8 rewrites
`Src.A.isNil` (an explicit `casesOn`) and the matcher of `Src.B.isNil` onto the Ix `casesOn` of
the class. Decision 5 (D1): the rewrites go to the canonical forms `Src.A.isNil._ix`,
`Src.B.isNil.match_1._ix`, which are the bytes of `Can`, where the class is declared once; the Lean
names keep their baselines (recorded `PJ-FORM-O8`; `Src.B.isNil`, an ordinary caller of its
matcher, `INHERITED`). `Src.Z` is a
singleton class next to the collapsed `X`, `Y` (a lifted slot): O8 rewrites the matcher of
`Src.Z.isE` too (`Can` declares `X`, `Z`). `Src.A.isNil'` has a caller that states its open
unfolding against Lean's `casesOn` (`isNil'_unfold`, proved by `rfl`): the Lean name keeps its
form, so the caller checks; nothing about it is read, and `Src.A.isNil'._ix` is canonical like
`Src.A.isNil._ix`. Lean's own `A.noConfusionType` gets a canonical form too; Lean's
`A.noConfusion` keeps referring to the unchanged Lean name. Value pins by `rfl` over every function. -/
set_option Elab.async false

namespace PassO8
namespace Src
mutual
inductive A
  | nil : A
  | a : B → A
inductive B
  | nil : B
  | b : A → B
end

def A.isNil (x : A) : Bool := @A.casesOn (fun _ => Bool) x true (fun _ => false)

def B.isNil : B → Bool
  | .nil => true
  | .b _ => false

theorem isNil_nil : A.isNil .nil = true := rfl
theorem isNil_a : A.isNil (.a .nil) = false := rfl
theorem B_isNil_b : B.isNil (.b .nil) = false := rfl

/-- A caller that unfolds `A.isNil'` against Lean's `casesOn` shape: it checks because the
Lean name keeps its form (D1); the canonical form is `A.isNil'._ix`. -/
def A.isNil' (x : A) : Bool := @A.casesOn (fun _ => Bool) x true (fun _ => false)
theorem isNil'_unfold (x : A) :
    A.isNil' x = @A.casesOn (fun _ => Bool) x true (fun _ => false) := rfl

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

def Z.isE : Z → Bool
  | .e => true
  | .n _ _ => false

theorem isE_e : Z.isE .e = true := rfl
theorem isE_n : Z.isE (.n .z .z) = false := rfl
end Src

namespace Can
inductive A
  | nil : A
  | a : A → A

def A.isNil (x : A) : Bool := @A.casesOn (fun _ => Bool) x true (fun _ => false)

def B.isNil : A → Bool
  | .nil => true
  | .a _ => false

theorem isNil_nil : A.isNil .nil = true := rfl
theorem isNil_a : A.isNil (.a .nil) = false := rfl
theorem B_isNil_b : B.isNil (.a .nil) = false := rfl

def A.isNil' (x : A) : Bool := @A.casesOn (fun _ => Bool) x true (fun _ => false)
theorem isNil'_unfold (x : A) :
    A.isNil' x = @A.casesOn (fun _ => Bool) x true (fun _ => false) := rfl

mutual
inductive X
  | z : X
  | s : Z → X
inductive Z
  | n : X → X → Z
  | e : Z
end

def Z.isE : Z → Bool
  | .e => true
  | .n _ _ => false

theorem isE_e : Z.isE .e = true := rfl
theorem isE_n : Z.isE (.n .z .z) = false := rfl
end Can
end PassO8
