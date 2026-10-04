/- A6p per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O11b, `noConfusion` of a split-off member in enumeration form. In `Src`, `B` (one constructor,
no fields) does not mention `A`, so Pass 1 splits it off; inside the mutual block Lean gave it the
general `noConfusionType`/`noConfusion`, while `Can`, which declares `B` alone, has Lean's
enumeration form. O11b gives `Src.B.noConfusionType` and `Src.B.noConfusion` the enumeration form:
the twin pairs are byte-equal with the switch on. `Src.E` has two constructors (enumeration form
`noConfusionTypeEnum E.ctorIdx`): O11b declines (`PENDING-NOCONFUSION`, the scheduling edge).
Value pins by `rfl`, and a `noConfusion` user. -/
set_option Elab.async false

namespace PassO11b
namespace Src
mutual
inductive A
  | nil : A
  | a : B → A → A
  | e : E → A
inductive B
  | nil : B
inductive E
  | x : E
  | y : E
end

theorem nc (P : Prop) (p : P) : B.noConfusion (P := P) (rfl : B.nil = B.nil) p = p := rfl
theorem exy : E.x ≠ E.y := fun h => E.noConfusion h
def B.val : B → Nat
  | .nil => 7
theorem val_nil : B.val .nil = 7 := rfl
end Src

namespace Can
inductive B
  | nil : B
inductive E
  | x : E
  | y : E
inductive A
  | nil : A
  | a : B → A → A
  | e : E → A

theorem nc (P : Prop) (p : P) : B.noConfusion (P := P) (rfl : B.nil = B.nil) p = p := rfl
theorem exy : E.x ≠ E.y := fun h => E.noConfusion h
def B.val : B → Nat
  | .nil => 7
theorem val_nil : B.val .nil = 7 := rfl
end Can
end PassO11b
