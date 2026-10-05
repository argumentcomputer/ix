import Tests.Ix.CompileCert.SourceModels

namespace Tests.Ix.CompileCert.SourceBasis
open _root_.Ix.CompileCert

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"source basis control failed: {label}")

def run : IO Unit := do
  let env ← getCompileEnv #[Compiled.prefixName]
  let root := Compiled.prefixName ++ `Node.val
  for (selected, expected) in
      [([root], [_root_.Ix.Kernel.BasisKind.falseK]),
       ([root, `False, `Eq], []),
       ([`True], [.falseK, .eqK])] do
    let captured ← IO.ofExcept (captureCone env.find? selected 256)
    let installed ← match installSourceNormalized captured.source selected with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError (SourceModels.label error))
    require "only missing fixed bases appended" (decide (installed.semanticSupport.basisSupport = expected))
    require "every normalized record/name/order retained"
      (decide (installed.declarations.take installed.normalizedDeclarations.length = installed.normalizedDeclarations))
    require "False present at exact source pin" (checkInstalledPin installed.env id _root_.Ix.Kernel.falseName 0)
    require "Eq present at exact source pin" (checkInstalledPin installed.env id _root_.Ix.Kernel.eqName 1)
    require "all appended bases are finite and closed"
      (installed.semanticSupport.basisSupport.all sourceBasisSupportClosed)
    IO.println s!"PASS: {selected}: 5 basis completion controls; added={repr expected}"
  let raw ← IO.ofExcept (captureCone env.find? [root] 256)
  for name in [`False, `Eq] do
    let conflict : Lean.ConstantInfo := .axiomInfo {
      name, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
    let source : Source := ⟨raw.source.declarations ++ [conflict]⟩
    match installSourceNormalized source [root] with
    | .error (.checking error position) =>
      IO.println s!"PASS: conflicting original {name} retained and refused by fold at {position}: {error}"
    | .error error => throw (IO.userError s!"conflicting original did not reach verified fold: {SourceModels.label error}")
    | .ok _ => throw (IO.userError s!"conflicting original {name} was accepted")

end Tests.Ix.CompileCert.SourceBasis
def main : IO Unit := Tests.Ix.CompileCert.SourceBasis.run
