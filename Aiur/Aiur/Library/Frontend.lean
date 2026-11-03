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
