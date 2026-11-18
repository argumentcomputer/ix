import Aiur.Tiling.Enables
import Aiur.Tiling.Ixa

/-!
# A faster `checkEnables`, proved equal

`boolDirect cs e` compares the normal form of every constraint of `cs` with
two polynomials built from `e`, and `checkEnables` asks it for every enable,
every variable near an enable and every one-hot candidate: the constraints'
normal forms are recomputed on every query. The `…N` functions below take the
normal forms `norms cs` computed once per chip and are otherwise the same
definitions; `checkEnables_eq` and `IChip.checkEnables_eq` are `@[csimp]`, so
compiled code runs `checkEnablesN` wherever `checkEnables` is called, with no
change to any statement.
-/

namespace Aiur.Tiling.Bridge

open Aiur.Circuit
open Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

/-- The normal form of every constraint. -/
def norms (cs : List (ArithExpr F)) : List (Poly F) := cs.map fun c => Poly.norm (Poly.ofExpr c)

def boolDirectN (ns : List (Poly F)) (e : ArithExpr F) : Bool :=
  Poly.Identical (Poly.ofExpr e) ([] : Poly F) || Poly.Identical (Poly.ofExpr e) (Poly.const 1) ||
    let a := Poly.norm (Poly.ofExpr (boolExpr e))
    let b := Poly.norm (Poly.ofExpr (.sub e (.mul e e)))
    ns.any fun n => n == a || n == b

theorem boolDirectN_eq (cs : List (ArithExpr F)) (e : ArithExpr F) :
    boolDirectN (norms cs) e = boolDirect cs e := by
  simp [boolDirectN, boolDirect, norms, Poly.Identical, List.any_map, Function.comp_def]

def boolCertN (ns : List (Poly F)) : ArithExpr F → Bool
  | .mul x y => boolDirectN ns (.mul x y) || (boolCertN ns x && boolCertN ns y)
  | .sub x y => boolDirectN ns (.sub x y) ||
      (Poly.Identical (Poly.ofExpr x) (Poly.const 1) && boolCertN ns y)
  | e => boolDirectN ns e

theorem boolCertN_eq (cs : List (ArithExpr F)) : ∀ e, boolCertN (norms cs) e = boolCert cs e
  | .mul x y => by simp only [boolCertN, boolCert, boolDirectN_eq, boolCertN_eq cs x, boolCertN_eq cs y]
  | .sub x y => by simp only [boolCertN, boolCert, boolDirectN_eq, boolCertN_eq cs y]
  | .const _ => by simp only [boolCertN, boolCert, boolDirectN_eq]
  | .var _ => by simp only [boolCertN, boolCert, boolDirectN_eq]
  | .add _ _ => by simp only [boolCertN, boolCert, boolDirectN_eq]

def boolSumN (cs : List (ArithExpr F)) (ns : List (Poly F)) (bound : Nat) (e : ArithExpr F) : Bool :=
  match addVars e with
  | none => false
  | some I => decide I.Nodup && cs.any fun c =>
      let J := (varsOf c).dedup
      I.all (· ∈ J) && J.all (fun j => boolDirectN ns (.var j)) && boolDirectN ns (sumExpr J) &&
        decide (J.length < bound)

theorem boolSumN_eq (cs : List (ArithExpr F)) (bound : Nat) (e : ArithExpr F) :
    boolSumN cs (norms cs) bound e = boolSum cs bound e := by
  unfold boolSumN boolSum
  simp only [boolDirectN_eq]
  rfl

def boolLinearN (cs : List (ArithExpr F)) (ns : List (Poly F)) (bound : Nat) (e : ArithExpr F) : Bool :=
  let I := (varsOf e).dedup
  !I.isEmpty && boolSumN cs ns bound (addOf I) &&
    (Poly.Identical (Poly.ofExpr e) (Poly.ofExpr (addOf I)) ||
      Poly.Identical (Poly.ofExpr e) (Poly.ofExpr (.sub (.const 1) (addOf I))))

theorem boolLinearN_eq (cs : List (ArithExpr F)) (bound : Nat) (e : ArithExpr F) :
    boolLinearN cs (norms cs) bound e = boolLinear cs bound e := by
  simp only [boolLinearN, boolLinear, boolSumN_eq]

def boolVarsN (cs : List (ArithExpr F)) (ns : List (Poly F)) (e : ArithExpr F) : List Var :=
  let E := (varsOf e).dedup
  let near := cs.filter fun c => (varsOf c).any (· ∈ E)
  (E ++ near.flatMap varsOf).dedup.filter fun v => boolDirectN ns (.var v)

theorem boolVarsN_eq (cs : List (ArithExpr F)) (e : ArithExpr F) :
    boolVarsN cs (norms cs) e = boolVars cs e := by
  simp only [boolVarsN, boolVars, boolDirectN_eq]

def boolEnumN (cs : List (ArithExpr F)) (ns : List (Poly F)) (e : ArithExpr F) : Bool :=
  let V := boolVarsN cs ns e
  let C := cs.filter fun c => (varsOf c).all (· ∈ V)
  decide (V.length ≤ 12) && (varsOf e).all (· ∈ V) &&
    V.sublists.all fun S =>
      !(C.all fun c => decide (c.denote (indicator S) = 0)) ||
        decide (e.denote (indicator S) = 0) || decide (e.denote (indicator S) = 1)

theorem boolEnumN_eq (cs : List (ArithExpr F)) (e : ArithExpr F) :
    boolEnumN cs (norms cs) e = boolEnum cs e := by
  simp only [boolEnumN, boolEnum, boolVarsN_eq]

def boolAnyN (cs : List (ArithExpr F)) (ns : List (Poly F)) (bound : Nat) (e : ArithExpr F) : Bool :=
  boolCertN ns e || boolSumN cs ns bound e || boolLinearN cs ns bound e || boolEnumN cs ns e

theorem boolAnyN_eq (cs : List (ArithExpr F)) (bound : Nat) (e : ArithExpr F) :
    boolAnyN cs (norms cs) bound e = boolAny cs bound e := by
  simp only [boolAnyN, boolAny, boolCertN_eq, boolSumN_eq, boolLinearN_eq, boolEnumN_eq]

def boolCertAtN (cs : List (ArithExpr F)) (ns : List (Poly F)) (bound : Nat) (sel : Var)
    (e : ArithExpr F) : Bool :=
  boolAnyN cs ns bound e ||
    (let split := Poly.norm (Poly.ofExpr (.mul (.sub (.const 1) (.var sel)) e))
     (ns.any fun n => n == split) && boolAnyN cs ns bound (substVar sel 1 e))

theorem boolCertAtN_eq (cs : List (ArithExpr F)) (bound : Nat) (sel : Var) (e : ArithExpr F) :
    boolCertAtN cs (norms cs) bound sel e = boolCertAt cs bound sel e := by
  simp only [boolCertAtN, boolCertAt, boolAnyN_eq]
  simp [norms, Poly.Identical, List.any_map, Function.comp_def]

def checkEnablesN (bound : Nat) (c : Chip F) : Bool :=
  let a := Activation.compile c
  let ns := norms a.constraints
  a.sends.all (fun s => boolCertAtN a.constraints ns bound c.numVars s.enable) &&
    a.memory.all (fun m => boolCertAtN a.constraints ns bound c.numVars m.enable)

@[csimp] theorem checkEnables_eq : @checkEnables = @checkEnablesN := by
  funext F _ _ bound c
  simp only [checkEnables, checkEnablesN, boolCertAtN_eq]

end Aiur.Tiling.Bridge

namespace Aiur.Tiling.Ixa

open Aiur.Tiling.Bridge

variable {F : Type} [Field F] [DecidableEq F]

def IChip.checkEnablesN (bound : Nat) (x : IChip F) : Bool :=
  let ns := norms x.constraints
  x.sends.all (fun s => boolCertAtN x.constraints ns bound x.activation s.enable) &&
    x.memory.all (fun m => boolCertAtN x.constraints ns bound x.activation m.enable)

@[csimp] theorem IChip.checkEnables_eq : @IChip.checkEnables = @IChip.checkEnablesN := by
  funext F _ _ bound x
  simp only [IChip.checkEnables, IChip.checkEnablesN, boolCertAtN_eq]

end Aiur.Tiling.Ixa
