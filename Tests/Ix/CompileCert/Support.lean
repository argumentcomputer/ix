import Tests.Ix.CompileCert.Direct

namespace Tests.Ix.CompileCert.Support

open _root_.Ix.CompileCert

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"support control failed: {label}")

def run : IO Unit := do
  let accepted ← match checkCompiled Direct.choiceInput with
    | .ok receipt => pure receipt
    | .error _ => throw (IO.userError "original compiler artifact did not admit")
  let cx : ExportContext := ⟨Direct.choiceInput.source, Direct.choiceInput.map, accepted.pins⟩
  let originalName ← match cx.name `first with
    | .ok name => pure name
    | .error reason => throw (IO.userError reason)
  let some (.defnInfo header value hint) := accepted.env.find? originalName
    | throw (IO.userError "actual original definition missing")
  let helperHeader := { header with name := sourceName `CertifierHelper }
  let helper := _root_.Ix.Kernel.Declaration.defnDecl helperHeader value hint
  let support ← match checkAdmittedSupport accepted.toAdmittedArtifact #[helper] with
    | .ok receipt => pure receipt
    | .error _ => throw (IO.userError "fresh checked support definition failed")
  require "fresh helper actually installed" (support.env.find? helperHeader.name).isSome
  require "all complete original rows preserved" (decide (InstalledRowsPreserved accepted.env support.env))
  require "original semantic identity association checks separately"
    (checkInstalledAssociation accepted.env support.env id == some true)
  require "original bytes remain independently admitted" (checkCompiled Direct.choiceInput).isOk
  require "original name collision rejected" (match checkAdmittedSupport accepted.toAdmittedArtifact
      #[.defnDecl header value hint] with | .error .conflictingNames => true | _ => false)
  require "duplicate support name rejected" (match checkAdmittedSupport accepted.toAdmittedArtifact
      #[helper, helper] with | .error .conflictingNames => true | _ => false)
  require "wrong support body rejected by actual fold" (match checkAdmittedSupport accepted.toAdmittedArtifact
      #[.defnDecl helperHeader (.sort .zero) hint] with | .error (.checking ..) => true | _ => false)
  require "missing helper dependency rejected by actual fold" (match checkAdmittedSupport accepted.toAdmittedArtifact
      #[.defnDecl helperHeader (.const (sourceName `MissingSupport) []) hint] with
      | .error (.checking ..) => true | _ => false)
  require "empty separate support preserves original admission"
    (checkAdmittedSupport accepted.toAdmittedArtifact #[]).isOk
  IO.println "separate admitted target support: 9 controls passed"

end Tests.Ix.CompileCert.Support

def main : IO Unit := Tests.Ix.CompileCert.Support.run
