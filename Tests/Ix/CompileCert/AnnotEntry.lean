import Ix.CompileCert.AnnotEntry

namespace Tests.Ix.CompileCert.AnnotEntry
open _root_.Ix.CompileCert
open _root_.Ix.Kernel

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"annotated entry control: {label}")

def run : IO Unit := do
  let source ← match Cached.checkDecls .verified [] #[Declaration.basisDecl .falseK, .basisDecl .eqK] with
    | .ok result => pure result
    | .error _ => throw (IO.userError "independent source basis fold failed")
  let target ← match Cached.checkDecls .verified []
      #[Declaration.basisDecl .falseK, .basisDecl .eqK, .basisDecl .natK] with
    | .ok result => pure result
    | .error _ => throw (IO.userError "independent target extra-support fold failed")
  require "real source lacks literal Nat support" (!natLitSupported source)
  require "real target has extra literal Nat support" (natLitSupported target)
  require "global sufficient guard would reject" (!checkLiteralSupport source target)
  require "original complete installed association accepts" (checkInstalledAssociation source target id == some true)
  require "new complete annotated association accepts extra support" (checkAnnotatedAssociation source target id == some true)
  require "all source type guards accept" (checkTypeLiteralSupport source target)
  require "all source definition guards accept" (checkDefinitionLiteralSupport source target)
  require "missing actual target member still refuses"
    (checkAnnotatedAssociation source ⟨target.consts.filter (fun entry => entry.name != eqReflName)⟩ id != some true)
  IO.println s!"annotated entry: 8 controls passed; source rows={source.consts.length}, target rows={target.consts.length}"

#eval run

end Tests.Ix.CompileCert.AnnotEntry
