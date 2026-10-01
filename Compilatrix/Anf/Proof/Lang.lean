import Compilatrix.Anf.Proof.Mono
import Compilatrix.Sem.TracedTransform

/-! # Anf as a language

Anf programs run from a root on `Nat` arguments (`Sem.Lang`, the input
`(root index, arguments)` that SrcEval and Lam use), with values observed
program-independently: literals, and constructor trees tagged by the source
constructor (as Lam's `obsV`, M2.2). Every Anf pass's refinement (M2.3) is
stated against this instance; through `Lang.instTLang` it is also a traced
language with `Env := Unit`, `E := Empty` (decision D-1). -/

set_option autoImplicit false

namespace Compilatrix.Anf

open Compilatrix.Sem (Result ClockMono Obs Lang)

mutual

/-- A program-independent observation of an Anf value. -/
def obsV : Val → Option Obs
  | .lit (.nat n) => some (.nat n)
  | .lit (.str s) => some (.bytes s.toUTF8.toList)
  | .con (.src c) fs => (obsList fs).map (.ctor c)
  | _ => none

def obsList : List Val → Option (List Obs)
  | [] => some []
  | v :: vs =>
    match obsV v, obsList vs with
    | some o, some os => some (o :: os)
    | _, _ => none

end

/-- A run from the root at index `i.1` on `Nat` arguments `i.2`. -/
def anfRun (P : Program) (i : Nat × List Nat) (k : Nat) : Result Val :=
  match P.roots[i.1]? with
  | some g => run P k g (i.2.map fun n => .lit (.nat n))
  | none => .stuck

instance : Lang (Nat × List Nat) Program where
  Val := Val
  run := anfRun
  mono P i := by
    unfold anfRun
    split
    · exact run_mono P _ _
    · exact ClockMono.const _
  obs := obsV

theorem lang_run (P : Program) (i : Nat × List Nat) : Lang.run P i = anfRun P i := rfl

end Compilatrix.Anf
