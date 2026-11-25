import IxCC.Recheck.Run

/-!
# The recheck path up to Fir

`Recheck.runFir`: the front half of `Recheck.runLir` up to and including
`Fir.lower`, and nothing after it. Fir is where a back end that is not the
native one branches off (the lowering to Formal Aiur, package `IxCCAiur`): it
is the last level whose semantics is over values, before ownership and
reference counting (`Own`), the control-flow graph (`Cfg`) and the runtime
(`Rt`).

It runs the same steps as `runLir` in the same order (`front`, `Lam.erase`,
`anfOf`, `Fir.lower`), so a program `runLir` accepts has the same levels here
(`Recheck.runLir_runFir`). It leaves out what only the native back end needs:
`Own.immortal`, `Cfg.lower`, the roots' parameter check (`checkParams`, the
entry wrapper's `maxParams`), the switch check and `Rt.lower`.
-/

set_option autoImplicit false

namespace IxCC.Recheck

/-- What the recheck path makes up to Fir: every level from the checked
source to the Fir program. -/
structure FrontFir where
  src : Src.Program
  checked : Src.Relevance.Checked
  lam : Lam.Program
  anf : Anf.Program
  fir : Fir.Program

/-- The inputs the theorems about a front half made up to Fir under
certificate `c` cover (`Recheck.Covered`, as `Front.Covered`). -/
def FrontFir.Covered (f : FrontFir) (c : Cert) : Nat × List Nat → Prop :=
  Recheck.Covered c.mid f.src f.lam f.anf

/-- The recheck path up to the Fir program: the front end, erasure, the
middle end with the closures step, and `Fir.lower`. -/
def runFir (cfg : Config) (P : Src.Program) (c : Cert) : Except Err FrontFir := do
  let (src, checked) ← front cfg P c
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let anf ← anfOf c src lam
  let fir ← (Fir.lower anf).mapError Err.ofFir
  pure { src, checked, lam, anf, fir }

end IxCC.Recheck
