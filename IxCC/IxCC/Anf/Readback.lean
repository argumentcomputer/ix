import IxCC.Anf.Semantics

/-! # Anf readback

First-order Anf values as shared observations (`Sem.Obs`), exactly as Lam's
readback (`Lam.readback`): a `Nat` literal is a `Nat`, a constructor is its
source tag (from the constructor table, which Anf carries unchanged from
Lam) with its kept fields, a string literal its UTF-8 bytes. Closures and □
have none. Equal Lam and Anf readback of related values is what the
differential tests compare and what adequacy (02 §7.2) concludes. -/

namespace IxCC.Anf

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

end IxCC.Anf
