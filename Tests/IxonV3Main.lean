import Tests.Ix.IxonV3
import Tests.Ix.IxonV3FFI
import Tests.Ix.IxonV3VM
import Tests.Ix.IxonV3Text
import Tests.Ix.ResourceAdmit
import Tests.Ix.ResourceAddressed
import Tests.Ix.ResourceValidate
import Tests.Ix.ContractTransport
import Tests.Ix.ContractPipeline
import Tests.Ix.ContractDecompile
import Tests.Ix.ClaimsV3
import Tests.Ix.Catalog
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver
import Tests.IxonV3Handoff

def main (args : List String) : IO Unit := do
  if args.contains "--export-handoff" then
    Tests.IxonV3Handoff.writeArtifacts "/tmp/ixon-v3-handoff"
  else
    Tests.IxonV3Handoff.check "Tests/Fixtures/ixon-v3/handoff"
  let cases ← Tests.IxonV3.readExprCases
  let checks ← Tests.IxonV3.runGolden cases
  IO.println s!"Ixon v3: {checks} golden byte and rejection checks passed"
  let ffiChecks ← Tests.IxonV3.runFFI cases
  IO.println s!"Ixon v3: {ffiChecks} FFI, byte parity, and sharing hash checks passed"
  let vmChecks ← Tests.IxonV3.runVM cases
  IO.println s!"Ixon v3: {vmChecks} VM execution, interpretation, and proof checks passed"
  let textChecks ← Tests.IxonV3.runText
  IO.println s!"Ixon v3: {textChecks} text contract and rejection checks passed"
  Tests.Resource.run
  Tests.Resource.runAdmission
  Tests.ResourceAddressed.run
  Tests.ResourceValidate.run
  Tests.ContractTransport.run
  Tests.ContractPipeline.run
  Tests.ContractDecompile.run
  Tests.ClaimsV3.run
  let result ← LSpec.lspecIO (.ofList [
    ("v3 catalogs", Tests.Ix.Catalog.suite),
    ("primitive addresses", Tests.Ix.Kernel.PrimAddrs.suite),
    ("source contracts", Tests.Ix.SourceContract.suite ++
      Tests.Ix.SourceContract.Driver.suite)]) []
  unless result == 0 do throw <| IO.userError "primitive or source contract regression"
  if args.contains "--primitives" then
    let bytes ← IO.FS.readBinFile "/tmp/ixon-v3-primitives.ixe"
    let env ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv bytes)
    IO.println s!"Validating {env.consts.size} constants from the primitive closure"
    let resolved ← IO.ofExcept (Ix.Resource.validate env (Ix.Resource.standardProfile env))
    IO.println s!"Validated {resolved.addresses.size} addressed interfaces"
