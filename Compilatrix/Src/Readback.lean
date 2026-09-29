import Compilatrix.Src.Value
import Compilatrix.Sem.Result

/-! # Readback

First-order SrcEval values as shared observations (`Sem.Obs`, design note
01 §3.1, 02 §5.2): a literal is a `Nat`, a constructor is its index with
its kept fields in order, a string literal its UTF-8 bytes. Which fields are
kept is the relevance check's `CtorRel` (`keep c i`); a kept field that holds
`irr` has no observation, so a wrong annotation cannot change a result by
dropping a field. Closures, partial applications and `irr` have none. -/

namespace Compilatrix.Src

open Compilatrix.Sem (Obs)

mutual

def readback (p : Program) (keep : CId → Nat → Bool) : Value → Option Obs
  | .lit n => some (.nat n)
  | .str s => some (.bytes s.toUTF8.toList)
  | .con c _ _ fs => do
    let tag := match p.decl? c with
      | some (.ctor _ _ _ cidx _ _ _) => cidx
      | _ => 0
    return .ctor tag (← readbackFields p keep c 0 fs)
  | _ => none

def readbackFields (p : Program) (keep : CId → Nat → Bool) (c : CId) (i : Nat) :
    List Value → Option (List Obs)
  | [] => some []
  | v :: vs => do
    let rest ← readbackFields p keep c (i + 1) vs
    if keep c i then return (← readback p keep v) :: rest else return rest

end

/-- Readback keeping every field (an `irr` field has no observation);
for programs without a relevance check. -/
def readbackAll (p : Program) : Value → Option Obs :=
  readback p (fun _ _ => true)

end Compilatrix.Src
