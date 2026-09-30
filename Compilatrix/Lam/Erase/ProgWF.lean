import Compilatrix.Lam.Erase.Input

/-! # The declarations erasure's proof assumes

`Input.progWF` decides the structural facts about the Src declarations
that erasure's correctness proof assumes (`Erase.Proof.ProgWF`, with
`progWF_iff`): every constructor is listed by its inductive at its index,
every listed constructor declares that inductive and index, and a
constructor's field classes, where annotated, are as many as its fields; a
recursor has a rule per constructor and at most one per minor, and a
subsingleton recursor has its minor and index fields within its indices;
the pinned `Nat`, `Bool` and `Decidable` constructors have their shapes.
Tc typing and the relevance check ensure all of it; erasure checks it
(`erase-progwf`). It reads every declaration once, through the persistent
map (D17). -/

namespace Compilatrix.Lam.Erase

open Compilatrix.Src

namespace Input

variable (I : Input)

/-- A constructor's inductive, index, parameter count and field count. -/
def ctorInfo? (c : CId) : Option (CId × Nat × Nat × Nat) :=
  match I.decl? c with
  | some (.ctor _ _ ind cidx np nf _) => some (ind, cidx, np, nf)
  | _ => none

/-- The facts about one declaration `c`. -/
def declWF (c : CId) : Decl → Bool
  | .ctor _ _ ind cidx _ nf _ =>
    (I.ctorsOf ind)[cidx]? == some c && (I.fields? c).all (·.length == nf)
  | .induct _ _ _ _ _ ctors =>
    ctors.zipIdx.all fun (k, i) =>
      match I.ctorInfo? k with
      | some (t, j, _, _) => t == c && j == i
      | none => false
  | .recr _ _ _ _ _ nmin ni ind rules _ =>
    decide ((I.ctorsOf ind).length ≤ rules.length) && decide (rules.length ≤ nmin) &&
      match I.recKind.get? c with
      | some (.subsingleton _ srcs) =>
        decide (0 < nmin) && srcs.all fun
          | .index i => decide (i < ni)
          | .proof => true
      | _ => true
  | _ => true

/-- A pinned `Nat` has its pinned `zero` (index 0) and `succ` (index 1, one
field), without parameters. -/
def natPinsOk : Bool :=
  match I.known.nat with
  | none => true
  | some N =>
    match I.known.natZero, I.known.natSucc with
    | some Z, some S => I.ctorInfo? Z == some (N, 0, 0, 0) && I.ctorInfo? S == some (N, 1, 0, 1)
    | _, _ => false

/-- A pinned `Nat.zero` has neither parameters nor fields. -/
def zeroPinOk : Bool :=
  match I.known.natZero with
  | none => true
  | some Z =>
    match I.ctorInfo? Z with
    | some (_, _, np, nf) => np == 0 && nf == 0
    | none => false

/-- A pinned `Nat.succ` has no parameters and one field. -/
def succPinOk : Bool :=
  match I.known.natSucc with
  | none => true
  | some S =>
    match I.ctorInfo? S with
    | some (_, _, np, nf) => np == 0 && nf == 1
    | none => false

/-- The pinned `Bool` constructors come together: `false` at index 0 and
`true` at index 1 of one inductive, without fields. -/
def boolPinsOk : Bool :=
  match I.known.boolFalse, I.known.boolTrue with
  | none, none => true
  | some f, some t =>
    match I.ctorInfo? f, I.ctorInfo? t with
    | some (B, i, _, nf), some (B', i', _, nf') =>
      B == B' && i == 0 && nf == 0 && i' == 1 && nf' == 0
    | _, _ => false
  | _, _ => false

/-- Two optional constructors are not constructors of one inductive. -/
def otherInd (c d : Option CId) : Bool :=
  match c.bind I.ctorInfo?, d.bind I.ctorInfo? with
  | some (ind, _), some (ind', _) => ind != ind'
  | _, _ => true

/-- `Decidable`'s pinned constructors belong to an inductive other than
those of the pinned `Bool` and `Nat` constructors. -/
def decOtherOk : Bool :=
  [I.known.decIsFalse, I.known.decIsTrue].all fun c =>
    [I.known.boolFalse, I.known.boolTrue, I.known.natZero, I.known.natSucc].all fun d =>
      I.otherInd c d

/-- An optional pinned constructor is a constructor at index `i`. -/
def ctorIdxOk (c : Option CId) (i : Nat) : Bool :=
  match c with
  | none => true
  | some c =>
    match I.ctorInfo? c with
    | some (_, j, _, _) => j == i
    | none => false

/-- Decide `Erase.Proof.ProgWF`. -/
def progWF : Bool :=
  (I.decls.toList.all fun (c, _) =>
    match I.decl? c with
    | some d => I.declWF c d
    | none => true) &&
  I.natPinsOk && I.zeroPinOk && I.succPinOk && I.boolPinsOk && I.decOtherOk &&
  I.ctorIdxOk I.known.decIsFalse 0 && I.ctorIdxOk I.known.decIsTrue 1

end Input

end Compilatrix.Lam.Erase
