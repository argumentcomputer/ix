import Ix.CompileCert.ValueReceipt

namespace Tests.Ix.CompileCert.ValueReceipt
open _root_.Ix.CompileCert
open _root_.Ix.Kernel

private def firstName := sourceName `CertificateValues.first
private def aliasName := sourceName `CertificateValues.alias
private def certificateName := sourceName `CertificateValues.equal
private def natType : Expr := .const natName []
private def functionType : Expr := .forallE natType natType ⟨.never⟩
private def firstHeader : ConstantVal := ⟨firstName, [], functionType⟩
private def aliasHeader : ConstantVal := ⟨aliasName, [], functionType⟩
private def request : ValueEquationRequest :=
  ⟨certificateName, [], .succ .zero, functionType, aliasName, [], firstName, []⟩
private def certificateHeader : ConstantVal := ⟨certificateName, [], request.type⟩
private def proof : Expr := Expr.mkAppN (.const eqReflName [.succ .zero])
  [functionType, .const firstName []]
private def prefixDecls : Array Declaration := #[.basisDecl .eqK, .basisDecl .natK,
  .defnDecl firstHeader (.lam natType (.bvar 0) ⟨.never⟩) (.regular 0),
  .defnDecl aliasHeader (.const firstName []) (.regular 1)]
private def declarations : Array Declaration := prefixDecls.push (.thmDecl certificateHeader proof)

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"value receipt control failed: {label}")
  IO.println s!"PASS: value receipt {label}"

def run : IO Unit := do
  let env ← match checked : Cached.checkDecls .verified [] declarations with
    | .ok result =>
      have _independent : ∀ (V : Type) [inst : SetTheory V], Nonempty (StrongInstalledModel V result) := by
        intro V inst
        exact strongInstalledModel_exists V [] declarations result checked
      pure result
    | .error (error, position) => throw (IO.userError s!"actual alias/equality fold failed at {position}: {error}")
  require "independent checked alias theorem" (readCheckedValueEndpoints env request).isSome
  let noTheorem := { env with consts := env.consts.filter (fun entry => entry.name != certificateName) }
  require "identity needs no extra theorem" (readCheckedValueEndpoints noTheorem
    { request with left := firstName, certificate := sourceName `AbsentCertificate }).isSome
  require "alias cannot borrow absent theorem" (!(readCheckedValueEndpoints noTheorem request).isSome)
  require "wrong endpoint refuses" (!(readCheckedValueEndpoints env
    { request with right := natZeroName }).isSome)
  require "wrong theorem carrier refuses" (!(readCheckedValueEndpoints env
    { request with carrier := natType }).isSome)
  require "wrong Eq universe refuses" (!(readCheckedValueEndpoints env
    { request with level := .zero }).isSome)
  require "wrong formal universe telescope refuses" (!(readCheckedValueEndpoints env
    { request with levelParams := [sourceName `u] }).isSome)
  require "wrong endpoint universe arity refuses" (!(readCheckedValueEndpoints env
    { request with leftLevels := [.zero] }).isSome)
  require "open request refuses" (!(readCheckedValueEndpoints env
    { request with carrier := .bvar 0 }).isSome)
  let wrongKind ← match Cached.checkDecls .verified []
      (prefixDecls.push (.defnDecl certificateHeader proof (.regular 2))) with
    | .ok result => pure result
    | .error (error, position) => throw (IO.userError s!"definition-kind control fold failed at {position}: {error}")
  require "checked definition does not impersonate theorem" (!(readCheckedValueEndpoints wrongKind request).isSome)
  require "unchecked forged theorem body fails actual fold"
    (match Cached.checkDecls .verified [] (prefixDecls.push (.thmDecl certificateHeader (.const natZeroName []))) with
     | .error _ => true
     | .ok _ => false)
  require "missing actual endpoint refuses" (!(readCheckedValueEndpoints
    { env with consts := env.consts.filter (fun entry => entry.name != aliasName) } request).isSome)
  let source ← match Cached.checkDecls .verified [] prefixDecls with
    | .ok result => pure result
    | .error _ => throw (IO.userError "independent source endpoint fold failed")
  require "actual source-map-bound alias receipt" (readCheckedMappedValue source env id aliasName firstName
    certificateName (.succ .zero) functionType).isSome
  require "changed source map cannot borrow theorem" (!(readCheckedMappedValue source env
    (fun name => if name == aliasName then natZeroName else name) aliasName firstName
    certificateName (.succ .zero) functionType).isSome)
  IO.println "value-equation receipts: 14/14 controls passed"

#eval run

end Tests.Ix.CompileCert.ValueReceipt
