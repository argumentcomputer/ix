import Aiur.Modules
import Lean.Elab.Eval

open Lean Elab Term in
/-- Elaborate a library fragment against its declared dependencies, retaining
only the fragment. Linking clients can then share each dependency exactly once. -/
elab "aiur_library% " dependencies:term:max source:str : term => do
  let dependencies ← unsafe evalTerm (Aiur.Modules.Program Nat)
    (mkApp (mkConst ``Aiur.Modules.Program) (mkConst ``Nat)) dependencies
  let program ← match Aiur.Modules.Frontend.parse (← getEnv) source.getString with
    | .ok program => pure program
    | .error error => throwErrorAt source "{error}"
  match Aiur.Modules.checkTemplates (dependencies.append program) with
  | .error error => throwErrorAt source "{error}"
  | .ok _ => return Lean.toExpr program

/-! The embedded forms. The fragment is written as Lean syntax, as in
`aiur⟦ … ⟧` (`Aiur.Modules.Frontend.embedded`), and lowered and checked as the
string form lowers and checks its text. -/
namespace Aiur.Library.Frontend
open Lean Elab Term Aiur.Modules.Frontend

/-- `aiur_library% deps ⟦ … ⟧`: the fragment, checked against `deps`, as
`aiur_library% deps "…"` checks its text. -/
syntax (name := embeddedLibrary) "aiur_library% " term:max "⟦" Aiur.Modules.Frontend.declsText "⟧" : term

/-- `aiur_library% ⟦ … ⟧`: a fragment that uses no other modules, checked on
its own, as `aiur% "…"` checks module text. -/
syntax (name := embeddedAlone) "aiur_library% " "⟦" Aiur.Modules.Frontend.declsText "⟧" : term

/-- Lower the fragment `text` (a `declsText` atom) and check it against
`dependencies`, retaining only the fragment. Linking clients can then share
each dependency exactly once. -/
def elabFragment (dependencies : Aiur.Modules.Program Nat) (stx text : Syntax) :
    TermElabM Lean.Expr := do
  let program ← match ofBlockText (← getEnv) text.getAtomVal with
    | .ok program => pure program
    | .error error => throwErrorAt stx "{error}"
  match Aiur.Modules.checkTemplates (dependencies.append program) with
  | .error error => throwErrorAt stx "{error}"
  | .ok _ => return Lean.toExpr program

@[term_elab embeddedLibrary]
def elabEmbeddedLibrary : TermElab := fun stx _ => uncounted do
  let dependencies ← unsafe evalTerm (Aiur.Modules.Program Nat)
    (mkApp (mkConst ``Aiur.Modules.Program) (mkConst ``Nat)) stx[1]
  elabFragment dependencies stx stx[3]

@[term_elab embeddedAlone]
def elabEmbeddedAlone : TermElab := fun stx _ => uncounted do
  elabFragment {} stx stx[2]

end Aiur.Library.Frontend
