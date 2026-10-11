import Ix.CompileCert.Entry

namespace Tests.Ix.CompileCert.InstalledFields
open _root_.Ix.CompileCert
open _root_.Ix.Kernel

def declaration (name : Lean.Name) : Declaration :=
  .defnDecl ⟨sourceName name, [], .sort (.succ .zero)⟩ (.sort .zero) (.regular 0)

def names (name : Name) : Name :=
  if name = sourceName `first ∨ name = sourceName `second then sourceName `shared else name

def require (label : String) (result : Bool) : IO Unit := do
  unless result do throw (IO.userError label)

/-- These positive environments come from two actual independent verified
folds. Mutation controls below intentionally need not be admitted. -/
def run : IO Unit := do
  let sourceStream := #[Declaration.basisDecl .falseK, .basisDecl .eqK,
    declaration `first, declaration `second]
  let targetStream := #[Declaration.basisDecl .falseK, .basisDecl .eqK, declaration `shared]
  let source ← match Cached.checkDecls .verified [] sourceStream with
    | .ok env => pure env
    | .error _ => throw (IO.userError "source verified fold failed")
  let target ← match Cached.checkDecls .verified [] targetStream with
    | .ok env => pure env
    | .error _ => throw (IO.userError "target verified fold failed")
  require "all actual telescopes" (checkTelescopes source target names)
  require "all actual types with both aliases" (checkInstalledTypes source target names)
  require "all actual definition bodies" (checkInstalledDefinitions source target names)
  require "actual False pin" (checkInstalledPin source names falseName 0)
  require "actual Eq pin" (checkInstalledPin source names eqName 1)
  require "missing target" (!checkInstalledTypes source Env.empty names)
  let badTypes : Env := ⟨source.consts.map fun entry =>
    if entry.name = sourceName `second then
      .defnInfo { entry.toConstantVal with type := .sort (.succ (.succ .zero)) } (.sort .zero) (.regular 0)
    else entry⟩
  require "second alias type cannot hide in first fiber" (!checkInstalledTypes badTypes target names)
  let badBodies : Env := ⟨source.consts.map fun entry =>
    if entry.name = sourceName `second then
      .defnInfo entry.toConstantVal (.sort (.succ .zero)) (.regular 0)
    else entry⟩
  require "second alias body cannot hide in first fiber" (!checkInstalledDefinitions badBodies target names)
  let theoremTarget : Env := ⟨target.consts.map fun entry => match entry with
    | .defnInfo header value _ => .thmInfo header value
    | other => other⟩
  require "theorem body is not a definition equation" (!checkInstalledDefinitions source theoremTarget names)
  let shadowed : Env := ⟨.defnInfo ⟨sourceName `second, [], .sort .zero⟩ (.sort .zero) (.regular 0) :: source.consts⟩
  require "shadowed actual source row" (!checkInstalledTypes shadowed target names)
  require "changed False identity" (!checkInstalledPin source (fun _ => sourceName `shared) falseName 0)
  require "wrong Eq arity" (!checkInstalledPin source names eqName 0)
  IO.println "installed fields: two independent verified folds; 12 controls passed"

end Tests.Ix.CompileCert.InstalledFields

def main : IO Unit := Tests.Ix.CompileCert.InstalledFields.run
