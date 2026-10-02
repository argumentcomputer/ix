import Tests.Ix.IxonV4
import Tests.Ix.IxonV4FFI
import Tests.Ix.IxonV4VM
import Tests.Ix.IxonText
import Tests.Ix.ResourceAdmit
import Tests.Ix.ResourceAddressed
import Tests.Ix.ResourceValidate
import Tests.Ix.ContractTransport
import Tests.Ix.ContractPipeline
import Tests.Ix.ContractDecompile
import Tests.Ix.ClaimsV4
import Tests.Ix.Catalog
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver
import Tests.IxonV4Handoff
import Tests.Ix.IxonV4Paths

def usage : String :=
  s!"usage: lake exe ixon-v4-tests [--export-fixtures] [--export-handoff] [--primitives]

Run the Ixon v4 codec, locality, claim, resource and cross-language transport
checks, and check the generated fixtures of Tests/Fixtures/ixon-v4/.

  --export-fixtures  write the generated text fixtures (claims, addressed
                     resources, resource cases) to ixon-v4-fixtures/ in the
                     scratch directory
  --export-handoff   write the handoff artifacts to ixon-v4-handoff/ in the
                     scratch directory instead of checking the checked-in ones
  --primitives       also validate the primitive closure that
                     `lake exe ixon-v4-primitives` wrote

{Tests.IxonV4.scratchUsage}"

/-- Write every generated text fixture of `Tests/Fixtures/ixon-v4/` (claims,
addressed resources, resource cases) from the producer its check compares
against, to `ixon-v4-fixtures/` in the scratch directory. `expressions.txt`
(independently specified bytes), `text.tsv` (text grammar sources) and
`primitives.tsv` (`ixon-v4-primitives`) are not generated here. -/
def exportFixtures (dir : System.FilePath) : IO Unit := do
  let out := Tests.IxonV4.fixtureExportDir dir
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "claims.tsv") Tests.ClaimsV4.fixtureText
  IO.FS.writeFile (out / "addressed.tsv")
    (← IO.ofExcept Tests.ResourceAddressed.fixtureText)
  IO.FS.writeFile (out / "resource.tsv") Tests.Resource.fixtureText
  IO.println s!"Exported claims.tsv, addressed.tsv and resource.tsv to {out}"

def main (args : List String) : IO Unit := do
  if args.contains "--help" then
    IO.println usage
    return
  let dir ← Tests.IxonV4.scratchDir
  if args.contains "--export-fixtures" then
    exportFixtures dir
  if args.contains "--export-handoff" then
    Tests.IxonV4Handoff.writeArtifacts (Tests.IxonV4.handoffExportDir dir)
  else
    Tests.IxonV4Handoff.check "Tests/Fixtures/ixon-v4/handoff"
  let cases ← Tests.IxonV4.readExprCases
  let checks ← Tests.IxonV4.runGolden cases
  IO.println s!"Ixon v4: {checks} golden byte and rejection checks passed"
  let ffiChecks ← Tests.IxonV4.runFFI cases
  IO.println s!"Ixon v4: {ffiChecks} FFI roundtrip and Lean/Rust byte parity checks passed"
  let vmChecks ← Tests.IxonV4.runVM cases
  IO.println s!"Ixon v4: {vmChecks} VM execution, interpretation, and proof checks passed"
  let textChecks ← Tests.IxonText.runText
  IO.println s!"Ixon text grammar {Ixon.Syntax.VERSION}: {textChecks} text contract and \
    rejection checks passed"
  Tests.Resource.run
  Tests.Resource.runAdmission
  Tests.ResourceAddressed.run
  Tests.ResourceValidate.run
  Tests.ContractTransport.run
  Tests.ContractPipeline.run
  Tests.ContractDecompile.run
  Tests.ClaimsV4.run
  let result ← LSpec.lspecIO (.ofList [
    ("catalogs", Tests.Ix.Catalog.suite),
    ("primitive addresses", Tests.Ix.Kernel.PrimAddrs.suite),
    ("source contracts", Tests.Ix.SourceContract.suite ++
      Tests.Ix.SourceContract.Driver.suite)]) []
  unless result == 0 do throw <| IO.userError "primitive or source contract regression"
  if args.contains "--primitives" then
    let bytes ← IO.FS.readBinFile (Tests.IxonV4.primitivesIxe dir)
    let env ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv bytes)
    IO.println s!"Validating {env.consts.size} constants from the primitive closure"
    let resolved ← IO.ofExcept (Ix.Resource.validate env (Ix.Resource.standardProfile env))
    IO.println s!"Validated {resolved.addresses.size} addressed interfaces"
