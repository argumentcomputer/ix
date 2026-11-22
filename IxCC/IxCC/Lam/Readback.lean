import IxCC.Lam.Semantics

/-! # Lam readback

First-order Lam values as shared observations (`Sem.Obs`): a `Nat` literal is a `Nat`, a constructor
is its source tag (the constructor index, from the program's constructor table) with its kept
fields, a string literal its UTF-8 bytes. Closures and □ have none.

This untyped readback equals `Src.readback` except on unboxed structures
(`Fin`, `Subtype`, one-method classes, …), which Lam represents by their one
kept field; the tests compare `readback (eraseVal v)` with the Lam result,
and Src's readback directly for `Nat` and `Bool` results. The typed readback
over first-order types is `Rt.readback`, at the machine level. -/

namespace IxCC.Lam

open IxCC.Sem (Obs)

mutual

def readback (P : Program) : Val → Option Obs
  | .lit (.nat n) => some (.nat n)
  | .lit (.str s) => some (.bytes s.toUTF8.toList)
  | .con c fs =>
    match P.ctor? c with
    | some info =>
      if info.arity == fs.length then (readbackList P fs).map (.ctor info.tag) else none
    | none => none
  | .clos .. | .box => none

def readbackList (P : Program) : List Val → Option (List Obs)
  | [] => some []
  | v :: vs =>
    match readback P v, readbackList P vs with
    | some o, some os => some (o :: os)
    | _, _ => none

end

end IxCC.Lam
