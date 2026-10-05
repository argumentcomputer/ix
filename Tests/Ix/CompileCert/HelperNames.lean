import Tests.Ix.CompileCert.SourceModels

namespace Tests.Ix.CompileCert.HelperNames

open _root_.Ix.CompileCert

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"helper-name control failed: {label}")

def run : IO Unit := do
  let env ← getCompileEnv #[Compiled.prefixName]
  for ownerLeaf in [`Node, `PolyNode] do
    let owner := Compiled.prefixName ++ ownerLeaf
    let captured ← IO.ofExcept (captureCone env.find? [owner ++ `val] 256)
    let installed ← match installSourceNormalized captured.source [owner ++ `val] with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError (SourceModels.label error))
    let sourceOwner := sourceName owner
    let sourceCtor := sourceName (owner ++ `mk)
    let targetOwner := sourceName `SyntheticTarget
    let targetCtor := targetOwner.num 7
    let original := captured.source.declarations.map fun ci =>
      let name := sourceName ci.name
      (name, if name == sourceOwner then targetOwner else if name == sourceCtor then targetCtor else name)
    let helpers ← IO.ofExcept (proposeSourceHelperBindings installed.modelProposal original)
    let names := sourceAndHelperNames original helpers
    require "original owner priority" (names sourceOwner == targetOwner)
    require "original constructor priority" (names sourceCtor == targetCtor)
    require "public model companion" (names (sourceOwner.str "_model") == targetOwner.str "_model")
    require "constructor model uses exact mapped constructor"
      (names (sourceCtor.str "_model") == targetCtor.str "_model")
    require "aux constructor uses mapped last component"
      (names (_root_.Ix.Kernel.Frontend.InModel.auxCtorName sourceOwner 0 sourceCtor) ==
        _root_.Ix.Kernel.Frontend.InModel.auxCtorName targetOwner 0 targetCtor)
    require "installed projection helper"
      (names (_root_.Ix.Kernel.projFnName sourceOwner 1) == _root_.Ix.Kernel.projFnName targetOwner 1)
    let forged := (sourceOwner.str "_model").str "UnproducedAmbientHelper"
    require "unproduced familiar prefix unchanged" (names forged == forged)
    require "helper cannot override original"
      (sourceAndHelperNames original ((sourceOwner, sourceName `Wrong) :: helpers) sourceOwner == targetOwner)
    require "conflicting source recipe refused"
      (match proposeSourceHelperBindings installed.modelProposal
        ((sourceOwner, sourceName `Wrong) :: original) with
        | .error _ => true | .ok _ => false)
    IO.println s!"PASS: {owner}: 9 source-recipe naming controls"

end Tests.Ix.CompileCert.HelperNames

def main : IO Unit := Tests.Ix.CompileCert.HelperNames.run
