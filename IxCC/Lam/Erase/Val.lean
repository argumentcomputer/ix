import IxCC.Lam.Erase.Input
import IxCC.Lam.Semantics
import IxCC.Src.Value

/-! # Erasing values

`eraseVal` (design note 02 §5.2) on first-order SrcEval values: `irr` is □,
a literal is a literal, a constructor keeps its fields kept at the profile
of its own levels (D18) under its checked key (`Decidable` retagged as
`Bool`), an unboxed structure is its kept field, and a quotient is its
unboxed element. Closures and partial applications have no image here:
their erasure depends on the context map of the term that built them
(erasure's Lam-only binders are captured), so M2.2 relates them up to
environment layout. The tests compare first-order results through this
function. -/

namespace IxCC.Lam.Erase

open IxCC.Src

mutual

def eraseVal (I : Input) : Value → Option Val
  | .lit n => some (.lit (.nat n))
  | .str s => some (.lit (.str s))
  | .irr .. => some .box
  | .con c ls _ fs =>
    let q := Profile.normalize (Src.profileOf ls) (I.lvls c)
    match I.decl? c with
    | some (.quot .ctor ..) => eraseNth I 0 fs
    | some (.ctor _ _ ind _ _ _ _) =>
      match I.unbox? ind q with
      | some j => eraseNth I j fs
      | none => (eraseKept I c q 0 fs).map (.con (I.ctorKey c))
    | _ => none
  | .clo .. | .pap .. => none

/-- The fields of constructor `c` kept at `q`, from index `i`. -/
def eraseKept (I : Input) (c : CId) (q : Profile) (i : Nat) : List Value → Option (List Val)
  | [] => some []
  | v :: vs => do
    let rest ← eraseKept I c q (i + 1) vs
    if I.kept c q i then return (← eraseVal I v) :: rest else return rest

/-- The `j`-th field. -/
def eraseNth (I : Input) : Nat → List Value → Option Val
  | _, [] => none
  | 0, v :: _ => eraseVal I v
  | j + 1, _ :: vs => eraseNth I j vs

end

end IxCC.Lam.Erase
